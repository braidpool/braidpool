from flask import Flask, jsonify, request
from flask_cors import CORS
import asyncio
from pydantic import ValidationError
import pyasic.config.temperature as _temp_mod
from pyasic.data.pools import PoolUrl
import urllib.parse
from pyasic import get_miner

_orig_from_bos = _temp_mod.TemperatureConfig.from_bosminer

def _coerce_floats_to_ints(obj):
    if isinstance(obj, dict):
        return {k: _coerce_floats_to_ints(v) for k, v in obj.items()}
    if isinstance(obj, list):
        return [_coerce_floats_to_ints(v) for v in obj]
    if isinstance(obj, float):              
        return int(round(obj))
    return obj

def _patched_from_bosminer(toml_conf):
    try:
        return _orig_from_bos(toml_conf)
    except ValidationError:
        coerced = _coerce_floats_to_ints(toml_conf)
        return _orig_from_bos(coerced)

_temp_mod.TemperatureConfig.from_bosminer = _patched_from_bosminer

_orig_pool_from_str = PoolUrl.from_str

@classmethod
def _patched_pool_from_str(cls, url_str):
    try:
        # Try the original parser first
        return _orig_pool_from_str(url_str)
    except ValidationError:
        if not url_str:
            return None

        parsed = urllib.parse.urlparse(url_str)

        # If no hostname at all → invalid
        if not parsed.hostname:
            return cls(scheme=None, host=None, port=None, pubkey=None)

        # Apply defaults only if missing
        scheme = parsed.scheme or "stratum+tcp"
        port = parsed.port
        if port is None:
            if scheme in ["stratum+tcp", "stratum"]:
                port = 4444
            elif scheme == "stratum+ssl":
                port = 4443
            else:
                port = 4444

        # Pubkey support
        pubkey = None
        if parsed.fragment:
            pubkey = parsed.fragment
        elif parsed.query:
            query_params = urllib.parse.parse_qs(parsed.query)
            pubkey = query_params.get('pubkey', [None])[0]

        return cls(scheme=scheme, host=parsed.hostname, port=port, pubkey=pubkey)

PoolUrl.from_str = _patched_pool_from_str


app = Flask(__name__)
CORS(app, resources={r"/api/*": {"origins": "*"}}) 


def normalize_data(data):
    def safe_int(val):
        try:
            return int(float(val)) if val is not None else None
        except Exception:
            return None

    def safe_float(val):
        try:
            return round(float(val), 2) if val is not None else None
        except Exception:
            return None

    temperature = None
    temperature_max = None
    vr_temperature = None
    
    # Temperatures
    hashboards = getattr(data, 'hashboards', [])
    if hashboards:
        asic_temps = []
        vr_temps = []
        for board in hashboards:
            if getattr(board, 'chip_temp', None) is not None:
                asic_temps.append(board.chip_temp)
            if getattr(board, 'temp', None) is not None:
                vr_temps.append(board.temp)
        if asic_temps:
            temperature = safe_float(sum(asic_temps) / len(asic_temps))
            temperature_max = safe_float(max(asic_temps))
        elif vr_temps:
            temperature = safe_float(vr_temps[0])
        if vr_temps:
            vr_temperature = safe_float(sum(vr_temps) / len(vr_temps))

    # Backup temp sources
    if temperature is None and hasattr(data, 'temperature_avg'):
        temperature = safe_float(getattr(data, 'temperature_avg'))
    if temperature is None and hasattr(data, 'env_temp'):
        temperature = safe_float(getattr(data, 'env_temp'))

    # Fans
    fans = getattr(data, 'fans', [])
    fan_speeds = [safe_int(fan.speed) for fan in fans if getattr(fan, 'speed', None) is not None]

    # Pools
    pools_data = []
    pools = getattr(data, 'pools', [])
    for pool in pools:
        pool_info = {
            "url": str(pool.url) if getattr(pool, 'url', None) else None,
            "user": getattr(pool, 'user', None),
            "status": getattr(pool, 'status', None)
        }
        if not pool_info["url"] or not pool_info["user"]:
            pool_info["status"] = "invalid"
        pools_data.append(pool_info)

    # Config fallback pools
    if not pools_data:
        config = getattr(data, 'config', None)
        if config and getattr(config, 'pools', None):
            pool_config = config.pools
            if hasattr(pool_config, 'groups'):
                for group in pool_config.groups:
                    if hasattr(group, 'pools'):
                        for pool in group.pools:
                            pool_info = {
                                "url": str(pool.url) if getattr(pool, 'url', None) else None,
                                "user": getattr(pool, 'user', None),
                                "status": "configured"
                            }
                            if not pool_info["url"] or not pool_info["user"]:
                                pool_info["status"] = "invalid"
                            pools_data.append(pool_info)

    # Primary pool selection 
    primary_pool = "No Pool"
    valid_pools = [p for p in pools_data if p.get("status") != "invalid" and p.get("url")]
    if valid_pools:
        try:
            url = valid_pools[0]["url"]
            parsed = urllib.parse.urlparse(url if url.startswith(('http', 'stratum')) else f'stratum+tcp://{url}')
            if parsed.hostname:
                primary_pool = parsed.hostname.replace('www.', '').split('.')[0].title()
        except:
            primary_pool = "Unknown Pool"

    # Normalized dict
    normalized = {
        "ip": getattr(data, "ip", None),
        "hostname": getattr(data, "hostname", None),
        "mac": getattr(data, "mac", None),
        "make": getattr(data, "make", None),
        "model": getattr(data, "model", None),
        "firmware": getattr(data, "fw_ver", None),
        "hashrate_current": safe_float(getattr(data, "raw_hashrate", None).rate if getattr(data, "raw_hashrate", None) else None),
        "hashrate_avg": safe_float(getattr(data, "hashrate", None).rate if getattr(data, "hashrate", None) else None),
        "expected_hashrate": safe_float(getattr(data, "expected_hashrate", None).rate if getattr(data, "expected_hashrate", None) else None),
        "temperature": temperature,
        "temperature_max": temperature_max,
        "vr_temperature": vr_temperature,
        "power_usage": safe_int(getattr(data, "wattage", None)),
        "power_limit": safe_int(getattr(data, "wattage_limit", None)) if hasattr(data, "wattage_limit") else None,
        "efficiency": safe_float(getattr(data, "efficiency_fract", None)),
        "voltage": safe_float(getattr(data, "voltage", None)) if hasattr(data, "voltage") else None,
        "fan_speeds": fan_speeds,
        "chip_count": safe_int(getattr(data, "total_chips", None)),
        "is_mining": getattr(data, "is_mining", None),
        "uptime": safe_int(getattr(data, "uptime", None)),
        "errors": getattr(data, "errors", []),
        "pools": pools_data,
        "primary_pool": primary_pool,
        "api_version": getattr(data, "api_ver", None),
        "timestamp": getattr(data, "timestamp", None),
    }
    return normalized


async def get_miner_data_async(ip):
    try:
        miner = await get_miner(ip)
        raw_data = await miner.get_data()
        normalized_data = normalize_data(raw_data)
        return {"success": True, "ip": ip, "data": normalized_data}
    except Exception as e:
        return {"success": False, "error": f"Failed to connect to miner at {ip}: {str(e)}"}


@app.route('/api/miners', methods=['GET'])
def get_miner_data():
    ip = request.args.get('ip')
    if not ip:
        return jsonify({"error": "IP parameter is required"}), 400

    try:
        result = asyncio.run(get_miner_data_async(ip))
    except Exception as e:
        return jsonify({"success": False, "error": str(e)}), 502

    if result["success"]:
        return jsonify(result)
    else:
        return jsonify(result), 502


if __name__ == '__main__':
    app.run(host='0.0.0.0', port=5001, debug=False)
