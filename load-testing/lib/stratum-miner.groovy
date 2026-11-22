import groovy.json.JsonSlurper
import groovy.json.JsonOutput
// Aliased so the class import doesn't shadow the pre-bound SampleResult (the parent sample)
import org.apache.jmeter.samplers.SampleResult as JMSampleResult

def host = vars.get("STRATUM_HOST") ?: "localhost"
def port = (vars.get("STRATUM_PORT") ?: "3333") as int
def workerName = vars.get("WORKER_NAME") ?: "miner0001.worker1"
def testDurationMs = ((vars.get("TEST_DURATION_SECONDS") ?: "300") as long) * 1000
def submitIntervalMs = (vars.get("SUBMIT_INTERVAL_MS") ?: "1000") as long
def socketTimeoutMs = 30000  // 30s read timeout for server pushes

def extranonce1 = ""
def extranonce2Size = 4
def currentJobId = null
def currentNtime = null
def requestId = 0
def versionRollingMask = null  // hex mask negotiated via mining.configure (null = not negotiated)
def responseLog = new StringBuilder()

// Per-request type statistics
def stats = [
    subscribe: [count: 0, success: 0, failed: 0, latencyMs: 0L],
    configure: [count: 0, success: 0, failed: 0, latencyMs: 0L],
    authorize: [count: 0, success: 0, failed: 0, latencyMs: 0L],
    submit: [count: 0, success: 0, failed: 0, accepted: 0, rejected: 0, latencies: []]
]
def firstRejectReason = null

// Server notification statistics
def notificationStats = [
    notifyCount: 0,
    uniqueJobs: new HashSet<String>(),
    setDifficultyCount: 0,
    lastDifficulty: null,
    difficulties: []
]


def nextId = { ++requestId }

def randomHex = { int numBytes ->
    def rand = new Random()
    def sb = new StringBuilder()
    numBytes.times { sb.append(String.format("%02x", rand.nextInt(256))) }
    return sb.toString()
}

def sendLine = { writer, Map request ->
    def jsonLine = JsonOutput.toJson(request)
    log.info("SEND [${workerName}]: ${jsonLine}")
    writer.write(jsonLine + "\n")
    writer.flush()
}

/**
 * Read one line from the socket. Returns parsed JSON map or null on timeout/EOF.
 */
def readOneLine = { reader ->
    try {
        def line = reader.readLine()
        if (line == null) return null
        log.info("RECV [${workerName}]: ${line}")
        return new JsonSlurper().parseText(line)
    } catch (java.net.SocketTimeoutException e) {
        return null
    }
}

/**
 * Record a protocol phase as a JMeter sub-result so per-phase latency shows up
 * as its own row (label "stratum.<phase>") in aggregate reports and the HTML
 * dashboard, instead of being buried inside the whole-session sample.
 */
def addPhaseResult = { String label, long startMs, long durationMs, boolean ok, String message ->
    def sub = new JMSampleResult()
    sub.setSampleLabel(label)
    sub.setStampAndTime(startMs, durationMs)
    sub.setSuccessful(ok)
    sub.setResponseCode(ok ? "200" : "500")
    sub.setResponseMessage(message ?: "")
    SampleResult.addSubResult(sub, false)  // false = keep our label, don't renumber
}

// Notification handler — updates currentJobId/currentNtime and tracks stats
def handleNotification = { msg ->
    def method = msg["method"] as String
    if (method == "mining.notify") {
        def params = msg["params"]
        if (params != null && params.size() > 0) {
            currentJobId = params[0] as String
            notificationStats.notifyCount++
            notificationStats.uniqueJobs.add(currentJobId)
            log.info("JOB [${workerName}]: received job_id=${currentJobId} (total: ${notificationStats.notifyCount}, unique: ${notificationStats.uniqueJobs.size()})")
        }
        if (params != null && params.size() > 7) {
            currentNtime = params[7] as String
        }
    } else if (method == "mining.set_difficulty") {
        def params = msg["params"]
        if (params != null && params.size() > 0) {
            notificationStats.setDifficultyCount++
            notificationStats.lastDifficulty = params[0]
            notificationStats.difficulties.add(params[0])
        }
        log.info("DIFF [${workerName}]: ${msg} (changes: ${notificationStats.setDifficultyCount})")
    }
}

/**
 * Read lines until we get a response with matching id, collecting any
 * server-push notifications along the way.
 */
def readResponseById = { reader, int expectedId ->
    def deadline = System.currentTimeMillis() + socketTimeoutMs
    while (System.currentTimeMillis() < deadline) {
        def msg = readOneLine(reader)
        if (msg == null) continue

        // Server push (has "method", no "id" or null "id")
        if (msg.containsKey("method") && (!msg.containsKey("id") || msg["id"] == null)) {
            handleNotification(msg)
            continue
        }
        // Response matching our request id
        if (msg.containsKey("id") && msg["id"] != null) {
            def msgId = msg["id"]
            // Handle both numeric and string id comparison
            if (msgId.toString() == expectedId.toString()) {
                return msg
            }
        }
    }
    return null
}


SampleResult.setSampleLabel("Stratum Miner Session - ${workerName}")
SampleResult.sampleStart()

def socket = null
def writer = null
def reader = null

try {
    log.info("CONNECT [${workerName}]: ${host}:${port}")
    socket = new java.net.Socket()
    socket.connect(new java.net.InetSocketAddress(host, port), 10000)
    socket.setSoTimeout(socketTimeoutMs)
    writer = new BufferedWriter(new OutputStreamWriter(socket.getOutputStream(), "UTF-8"))
    reader = new BufferedReader(new InputStreamReader(socket.getInputStream(), "UTF-8"))
    responseLog.append("Connected to ${host}:${port}\n")

    def subId = nextId()
    def subStartTime = System.currentTimeMillis()
    sendLine(writer, [id: subId, method: "mining.subscribe", params: []])
    def subResp = readResponseById(reader, subId)
    def subLatency = System.currentTimeMillis() - subStartTime
    
    stats.subscribe.count++
    stats.subscribe.latencyMs = subLatency

    if (subResp == null || subResp["result"] == null) {
        stats.subscribe.failed++
        addPhaseResult("stratum.subscribe", subStartTime, subLatency, false, "no response or null result")
        SampleResult.sampleEnd()
        SampleResult.setSuccessful(false)
        SampleResult.setResponseData("Subscribe failed: no response or null result", "UTF-8")
        SampleResult.setResponseCode("500")
        return
    }
    stats.subscribe.success++
    addPhaseResult("stratum.subscribe", subStartTime, subLatency, true, "ok")

    def subResultData = subResp["result"]
    if (subResultData instanceof List && subResultData.size() >= 3) {
        extranonce1 = subResultData[1] as String
        extranonce2Size = subResultData[2] as int
    }
    responseLog.append("Subscribed: extranonce1=${extranonce1}, extranonce2_size=${extranonce2Size} (${subLatency}ms)\n")
    log.info("SUBSCRIBED [${workerName}]: extranonce1=${extranonce1} latency=${subLatency}ms")

    def cfgId = nextId()
    def cfgStartTime = System.currentTimeMillis()
    sendLine(writer, [
        id: cfgId,
        method: "mining.configure",
        params: [["version-rolling"], ["version-rolling.mask": "1fffe000"]]
    ])
    def cfgResp = readResponseById(reader, cfgId)
    def cfgLatency = System.currentTimeMillis() - cfgStartTime
    
    stats.configure.count++
    stats.configure.latencyMs = cfgLatency
    
    if (cfgResp != null) {
        stats.configure.success++
        // Once version-rolling is negotiated, the server REQUIRES a 6th
        // version_bits param on every mining.submit — capture the mask.
        def cfgResult = cfgResp["result"]
        if (cfgResult instanceof Map && cfgResult["version-rolling"] == true) {
            versionRollingMask = cfgResult["version-rolling.mask"] as String
        }
        addPhaseResult("stratum.configure", cfgStartTime, cfgLatency, true, "ok")
        responseLog.append("Configured: ${JsonOutput.toJson(cfgResp)} (${cfgLatency}ms)\n")
        log.info("CONFIGURED [${workerName}]: ${cfgResp} mask=${versionRollingMask} latency=${cfgLatency}ms")
    } else {
        // Configure is optional - treat no response as success for stats
        stats.configure.success++
        addPhaseResult("stratum.configure", cfgStartTime, cfgLatency, true, "no response (optional)")
        responseLog.append("Configure: no response (optional, continuing) (${cfgLatency}ms)\n")
        log.info("CONFIGURE [${workerName}]: no response, continuing latency=${cfgLatency}ms")
    }

    def authId = nextId()
    def authStartTime = System.currentTimeMillis()
    sendLine(writer, [id: authId, method: "mining.authorize", params: [workerName, "x"]])
    def authResp = readResponseById(reader, authId)
    def authLatency = System.currentTimeMillis() - authStartTime
    
    stats.authorize.count++
    stats.authorize.latencyMs = authLatency

    if (authResp == null || authResp["result"] != true) {
        stats.authorize.failed++
        addPhaseResult("stratum.authorize", authStartTime, authLatency, false,
            authResp != null ? "rejected" : "no response")
        SampleResult.sampleEnd()
        SampleResult.setSuccessful(false)
        def authMsg = authResp != null ? JsonOutput.toJson(authResp) : "no response"
        SampleResult.setResponseData("Authorize failed: ${authMsg}", "UTF-8")
        SampleResult.setResponseCode("500")
        return
    }
    stats.authorize.success++
    addPhaseResult("stratum.authorize", authStartTime, authLatency, true, "ok")
    responseLog.append("Authorized: worker=${workerName} (${authLatency}ms)\n")
    log.info("AUTHORIZED [${workerName}] latency=${authLatency}ms")

    log.info("WAITING [${workerName}]: waiting for mining.notify...")
    def waitStartTime = System.currentTimeMillis()
    def jobDeadline = waitStartTime + 60000  // 60s max wait
    while (currentJobId == null && System.currentTimeMillis() < jobDeadline) {
        def msg = readOneLine(reader)
        if (msg == null) continue
        if (msg.containsKey("method") && (!msg.containsKey("id") || msg["id"] == null)) {
            handleNotification(msg)
        }
    }
    def firstNotifyLatency = System.currentTimeMillis() - waitStartTime

    if (currentJobId == null) {
        addPhaseResult("stratum.first_notify", waitStartTime, firstNotifyLatency, false, "timeout (60s)")
        SampleResult.sampleEnd()
        SampleResult.setSuccessful(false)
        SampleResult.setResponseData("Timeout waiting for mining.notify (60s)", "UTF-8")
        SampleResult.setResponseCode("500")
        return
    }
    addPhaseResult("stratum.first_notify", waitStartTime, firstNotifyLatency, true, "job_id=${currentJobId}")
    responseLog.append("First job received: job_id=${currentJobId} (${firstNotifyLatency}ms after authorize)\n")

    def sessionEnd = System.currentTimeMillis() + testDurationMs

    // Shorter timeout during submit loop to interleave notification reads
    socket.setSoTimeout(500)

    while (System.currentTimeMillis() < sessionEnd) {
        // Drain any pending notifications
        try {
            while (true) {
                def msg = readOneLine(reader)
                if (msg == null) break
                if (msg.containsKey("method") && (!msg.containsKey("id") || msg["id"] == null)) {
                    handleNotification(msg)
                }
            }
        } catch (Exception ignored) {}

        if (currentJobId == null) {
            Thread.sleep(submitIntervalMs)
            continue
        }

        def submitId = nextId()
        def extranonce2 = randomHex(extranonce2Size)
        def ntime = currentNtime ?: String.format("%08x", (long)(System.currentTimeMillis() / 1000))
        def nonce = randomHex(4)

        def submitParams = [workerName, currentJobId, extranonce2, ntime, nonce]
        if (versionRollingMask != null) {
            // Random bits ANDed with the mask satisfy the server's BIP310
            // precondition (version_bits & !mask == 0)
            def maskInt = (int) Long.parseLong(versionRollingMask, 16)
            def versionBits = new Random().nextInt() & maskInt
            submitParams.add(String.format("%08x", versionBits))
        }

        def submitStartTime = System.currentTimeMillis()
        sendLine(writer, [
            id: submitId,
            method: "mining.submit",
            params: submitParams
        ])

        // Longer timeout to wait for submit response
        socket.setSoTimeout(10000)
        def submitResp = readResponseById(reader, submitId)
        def submitLatency = System.currentTimeMillis() - submitStartTime
        socket.setSoTimeout(500)

        stats.submit.count++
        stats.submit.latencies.add(submitLatency)
        
        if (submitResp != null) {
            stats.submit.success++
            // Accepted = result:true; anything else (error, result:false/null) is
            // a rejection — expected for random nonces failing PoW, but the
            // reason is tracked so protocol-level failures are visible too.
            if (submitResp["result"] == true) {
                stats.submit.accepted++
            } else {
                stats.submit.rejected++
                if (firstRejectReason == null) {
                    firstRejectReason = JsonOutput.toJson(submitResp["error"] ?: submitResp)
                }
            }
            log.info("SUBMIT [${workerName}]: response=${submitResp} latency=${submitLatency}ms")
        } else {
            stats.submit.failed++
            log.warn("SUBMIT [${workerName}]: no response (timeout) latency=${submitLatency}ms")
        }
        // Rejections are expected (random nonces fail PoW) — only a missing
        // response marks the sub-result as failed
        def submitOutcome = submitResp == null ? "timeout"
            : (submitResp["result"] == true ? "accepted" : "rejected")
        addPhaseResult("stratum.submit", submitStartTime, submitLatency, submitResp != null, submitOutcome)

        // Throttle between submits
        if (submitIntervalMs > 0) {
            Thread.sleep(submitIntervalMs)
        }
    }

    SampleResult.sampleEnd()
    SampleResult.setSuccessful(true)
    
    def submitLatencies = stats.submit.latencies
    def submitMinLatency = submitLatencies.isEmpty() ? 0 : submitLatencies.min()
    def submitMaxLatency = submitLatencies.isEmpty() ? 0 : submitLatencies.max()
    def submitAvgLatency = submitLatencies.isEmpty() ? 0 : (submitLatencies.sum() / submitLatencies.size()).toLong()
    def submitP50Latency = 0L
    def submitP95Latency = 0L
    def submitP99Latency = 0L
    if (!submitLatencies.isEmpty()) {
        def sorted = submitLatencies.sort()
        submitP50Latency = sorted[(int)(sorted.size() * 0.50)]
        submitP95Latency = sorted[(int)(sorted.size() * 0.95)]
        submitP99Latency = sorted[(int)(sorted.size() * 0.99)]
    }
    
    def successRate = { s -> s.count > 0 ? String.format("%.1f", (s.success / s.count) * 100) : "N/A" }
    // ── Build Statistics Report ──────────────────────────────────────────────
    responseLog.append("\n═══════════════════════════════════════════════════════════════════════════════\n")
    responseLog.append("                         REQUEST STATISTICS                                    \n")
    responseLog.append("═══════════════════════════════════════════════════════════════════════════════\n")
    responseLog.append("\n┌─────────────────┬───────┬─────────┬────────┬────────────┬─────────────┐\n")
    responseLog.append("│ Request Type    │ Count │ Success │ Failed │ Success %  │ Latency(ms) │\n")
    responseLog.append("├─────────────────┼───────┼─────────┼────────┼────────────┼─────────────┤\n")
    responseLog.append(String.format("│ %-15s │ %5d │ %7d │ %6d │ %8s %% │ %11d │\n", 
        "subscribe", stats.subscribe.count, stats.subscribe.success, stats.subscribe.failed, 
        successRate(stats.subscribe), stats.subscribe.latencyMs))
    responseLog.append(String.format("│ %-15s │ %5d │ %7d │ %6d │ %8s %% │ %11d │\n", 
        "configure", stats.configure.count, stats.configure.success, stats.configure.failed, 
        successRate(stats.configure), stats.configure.latencyMs))
    responseLog.append(String.format("│ %-15s │ %5d │ %7d │ %6d │ %8s %% │ %11d │\n", 
        "authorize", stats.authorize.count, stats.authorize.success, stats.authorize.failed, 
        successRate(stats.authorize), stats.authorize.latencyMs))
    responseLog.append(String.format("│ %-15s │ %5d │ %7d │ %6d │ %8s %% │ avg: %6d │\n", 
        "submit", stats.submit.count, stats.submit.success, stats.submit.failed, 
        successRate(stats.submit), submitAvgLatency))
    responseLog.append("└─────────────────┴───────┴─────────┴────────┴────────────┴─────────────┘\n")
    
    responseLog.append("\nSubmit Latency Distribution:\n")
    responseLog.append(String.format("  min: %dms | p50: %dms | p95: %dms | p99: %dms | max: %dms\n",
        submitMinLatency, submitP50Latency, submitP95Latency, submitP99Latency, submitMaxLatency))

    responseLog.append("\nSubmit Outcomes:\n")
    responseLog.append("  accepted: ${stats.submit.accepted} | rejected: ${stats.submit.rejected} | no response: ${stats.submit.failed}\n")
    if (firstRejectReason != null) {
        responseLog.append("  first rejection reason: ${firstRejectReason}\n")
    }
    
    responseLog.append("\n┌─────────────────────┬───────┬──────────────────────────────────────────────┐\n")
    responseLog.append("│ Notification Type   │ Count │ Details                                      │\n")
    responseLog.append("├─────────────────────┼───────┼──────────────────────────────────────────────┤\n")
    responseLog.append(String.format("│ %-19s │ %5d │ unique_jobs: %-31d │\n", 
        "mining.notify", notificationStats.notifyCount, notificationStats.uniqueJobs.size()))
    responseLog.append(String.format("│ %-19s │ %5d │ last_difficulty: %-27s │\n", 
        "mining.set_difficulty", notificationStats.setDifficultyCount, 
        notificationStats.lastDifficulty ?: "N/A"))
    responseLog.append("└─────────────────────┴───────┴──────────────────────────────────────────────┘\n")
    
    responseLog.append("\nSession complete: ${stats.submit.count} submits, ${stats.submit.failed} errors\n")
    
    // ── Export Statistics as JMeter Variables ────────────────────────────────
    vars.put("STAT_SUBSCRIBE_COUNT", stats.subscribe.count.toString())
    vars.put("STAT_SUBSCRIBE_SUCCESS", stats.subscribe.success.toString())
    vars.put("STAT_SUBSCRIBE_FAILED", stats.subscribe.failed.toString())
    vars.put("STAT_SUBSCRIBE_LATENCY_MS", stats.subscribe.latencyMs.toString())
    
    vars.put("STAT_CONFIGURE_COUNT", stats.configure.count.toString())
    vars.put("STAT_CONFIGURE_SUCCESS", stats.configure.success.toString())
    vars.put("STAT_CONFIGURE_FAILED", stats.configure.failed.toString())
    vars.put("STAT_CONFIGURE_LATENCY_MS", stats.configure.latencyMs.toString())
    
    vars.put("STAT_AUTHORIZE_COUNT", stats.authorize.count.toString())
    vars.put("STAT_AUTHORIZE_SUCCESS", stats.authorize.success.toString())
    vars.put("STAT_AUTHORIZE_FAILED", stats.authorize.failed.toString())
    vars.put("STAT_AUTHORIZE_LATENCY_MS", stats.authorize.latencyMs.toString())
    
    vars.put("STAT_SUBMIT_COUNT", stats.submit.count.toString())
    vars.put("STAT_SUBMIT_SUCCESS", stats.submit.success.toString())
    vars.put("STAT_SUBMIT_FAILED", stats.submit.failed.toString())
    vars.put("STAT_SUBMIT_ACCEPTED", stats.submit.accepted.toString())
    vars.put("STAT_SUBMIT_REJECTED", stats.submit.rejected.toString())
    vars.put("STAT_SUBMIT_LATENCY_MIN_MS", submitMinLatency.toString())
    vars.put("STAT_SUBMIT_LATENCY_MAX_MS", submitMaxLatency.toString())
    vars.put("STAT_SUBMIT_LATENCY_AVG_MS", submitAvgLatency.toString())
    vars.put("STAT_SUBMIT_LATENCY_P50_MS", submitP50Latency.toString())
    vars.put("STAT_SUBMIT_LATENCY_P95_MS", submitP95Latency.toString())
    vars.put("STAT_SUBMIT_LATENCY_P99_MS", submitP99Latency.toString())
    
    vars.put("STAT_NOTIFY_COUNT", notificationStats.notifyCount.toString())
    vars.put("STAT_NOTIFY_UNIQUE_JOBS", notificationStats.uniqueJobs.size().toString())
    vars.put("STAT_SET_DIFFICULTY_COUNT", notificationStats.setDifficultyCount.toString())
    vars.put("STAT_LAST_DIFFICULTY", (notificationStats.lastDifficulty ?: "0").toString())
    
    SampleResult.setResponseData(responseLog.toString(), "UTF-8")
    SampleResult.setResponseCodeOK()
    log.info("DONE [${workerName}]: ${stats.submit.count} submits, ${stats.submit.failed} errors")
    log.info("STATS [${workerName}]: subscribe=${stats.subscribe.latencyMs}ms, configure=${stats.configure.latencyMs}ms, authorize=${stats.authorize.latencyMs}ms, submit_avg=${submitAvgLatency}ms")

} catch (Exception e) {
    log.error("ERROR [${workerName}]: ${e.message}", e)
    if (!SampleResult.isStampedAtStart()) {
        SampleResult.sampleStart()
    }
    SampleResult.sampleEnd()
    SampleResult.setSuccessful(false)
    responseLog.append("Exception: ${e.message}\n")
    responseLog.append(e.stackTrace.take(10).collect { it.toString() }.join('\n'))
    SampleResult.setResponseData(responseLog.toString(), "UTF-8")
    SampleResult.setResponseCode("500")
} finally {
    try { reader?.close() } catch (Exception ignored) {}
    try { writer?.close() } catch (Exception ignored) {}
    try { socket?.close() } catch (Exception ignored) {}
}
