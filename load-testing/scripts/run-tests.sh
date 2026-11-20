#!/usr/bin/env bash
# Orchestrator: setup → run JMeter tests → generate report → teardown
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LOAD_TEST_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
JMETER_DIR="$LOAD_TEST_DIR/jmeter"
REPORTS_DIR="$LOAD_TEST_DIR/reports"

# Which test to run (default: stratum-load-test)
TEST_PLAN="${1:-stratum-load-test}"
JMX_FILE="$JMETER_DIR/${TEST_PLAN}.jmx"

if [ ! -f "$JMX_FILE" ]; then
    echo "ERROR: Test plan not found: $JMX_FILE"
    echo "Available plans:"
    ls "$JMETER_DIR"/*.jmx 2>/dev/null | xargs -I{} basename {} .jmx
    exit 1
fi

# Check JMeter is installed — override via JMETER_BIN when not in PATH
JMETER_BIN="${JMETER_BIN:-$(command -v jmeter || true)}"
if [ -z "$JMETER_BIN" ] || ! command -v "$JMETER_BIN" &>/dev/null; then
    echo "ERROR: jmeter not found in PATH."
    echo "Install: https://jmeter.apache.org/download_jmeter.cgi"
    echo "Or set JMETER_BIN, e.g.: export JMETER_BIN=/opt/jmeter/bin/jmeter"
    exit 1
fi

# Always tear down the test environment, even if setup or JMeter fails
cleanup() {
    echo ""
    echo "[4/4] Tearing down..."
    "$SCRIPT_DIR/teardown.sh"
}
trap cleanup EXIT

# Prepare output directories
TIMESTAMP=$(date +%Y%m%d-%H%M%S)
RESULTS_FILE="$REPORTS_DIR/${TEST_PLAN}-${TIMESTAMP}.jtl"
DASHBOARD_DIR="$REPORTS_DIR/${TEST_PLAN}-${TIMESTAMP}-dashboard"

mkdir -p "$REPORTS_DIR"

echo "=== Braidpool Load Test Runner ==="
echo "Test plan:    $TEST_PLAN"
echo "Results:      $RESULTS_FILE"
echo "Dashboard:    $DASHBOARD_DIR/"
echo ""

# ── Step 1: Setup ─────────────────────────────────────────────────────────────
echo "[1/4] Setting up regtest environment..."
"$SCRIPT_DIR/setup-regtest.sh"

# Wait for first template to propagate
echo ""
echo "Waiting 5s for first block template to propagate..."
sleep 5

# ── Step 2: Run JMeter ───────────────────────────────────────────────────────
echo "[2/4] Running JMeter test: $TEST_PLAN"
echo ""

# || so a JMeter failure doesn't trip `set -e` before we can report and tear down
JMETER_EXIT=0
"$JMETER_BIN" -n \
    -t "$JMX_FILE" \
    -l "$RESULTS_FILE" \
    -Jtest.data.dir="$LOAD_TEST_DIR/data" \
    -Jtest.lib.dir="$LOAD_TEST_DIR/lib" \
    -e -o "$DASHBOARD_DIR" || JMETER_EXIT=$?

echo ""
if [ "$JMETER_EXIT" -eq 0 ]; then
    echo "JMeter completed successfully"
else
    echo "WARNING: JMeter exited with code $JMETER_EXIT"
fi

# ── Step 3: Summary ──────────────────────────────────────────────────────────
echo ""
echo "[3/4] Test Results Summary"
echo "─────────────────────────"

if [ -f "$RESULTS_FILE" ]; then
    TOTAL=$(tail -n +2 "$RESULTS_FILE" | wc -l)
    FAILURES=$(tail -n +2 "$RESULTS_FILE" | awk -F',' '{print $8}' | grep -c "false" || true)
    SUCCESS=$((TOTAL - FAILURES))
    if [ "$TOTAL" -gt 0 ]; then
        ERROR_RATE=$(awk "BEGIN {printf \"%.2f\", ($FAILURES/$TOTAL)*100}")
    else
        ERROR_RATE="N/A"
    fi
    echo "  Total samples:  $TOTAL"
    echo "  Successful:     $SUCCESS"
    echo "  Failed:         $FAILURES"
    echo "  Error rate:     ${ERROR_RATE}%"
else
    echo "  No results file found"
fi

echo ""
echo "  Full report:    $DASHBOARD_DIR/index.html"
echo "  Raw results:    $RESULTS_FILE"

# ── Step 4: Teardown runs via the EXIT trap ──────────────────────────────────
echo ""
echo "=== Done ==="
exit "$JMETER_EXIT"
