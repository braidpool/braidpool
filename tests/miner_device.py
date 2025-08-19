from flask import Flask, jsonify, request
from flask_cors import CORS
import asyncio
import json
from pydantic import ValidationError
import pyasic.config.temperature as _temp_mod

# Apply the same patches as your script
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
    except ValidationError as e:             
        coerced = _coerce_floats_to_ints(toml_conf)
        return _orig_from_bos(coerced)

_temp_mod.TemperatureConfig.from_bosminer = _patched_from_bosminer

from pyasic.data.pools import PoolUrl
import urllib.parse

_orig_pool_from_str = PoolUrl.from_str

@classmethod
def _patched_pool_from_str(cls, url_str):
    try:
        return _orig_pool_from_str(url_str)
    except ValidationError as e:
        if not url_str:
            return None
            
        parsed = urllib.parse.urlparse(url_str)
        scheme = parsed.scheme or "stratum+tcp"
        host = parsed.hostname
        port = parsed.port
        
        if port is None:
            if scheme in ["stratum+tcp", "stratum"]:
                port = 4444
            elif scheme == "stratum+ssl":
                port = 4443
            else:
                port = 4444
        
        pubkey = None
        if parsed.fragment:
            pubkey = parsed.fragment
        elif parsed.query:
            query_params = urllib.parse.parse_qs(parsed.query)
            pubkey = query_params.get('pubkey', [None])[0]
        
        return cls(scheme=scheme, host=host, port=port, pubkey=pubkey)

PoolUrl.from_str = _patched_pool_from_str

from pyasic import get_miner

app = Flask(__name__)
CORS(app)  

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
    
    hashboards = getattr(data, 'hashboards', [])
    if hashboards:
        asic_temps = []
        vr_temps = []
        
        for board in hashboards:
            if hasattr(board, 'chip_temp') and board.chip_temp is not None:
                asic_temps.append(board.chip_temp)
            if hasattr(board, 'temp') and board.temp is not None:
                vr_temps.append(board.temp)
        
        if asic_temps:
            temperature = safe_float(asic_temps[0])
            temperature_max = safe_float(max(asic_temps)) if len(asic_temps) > 1 else temperature
        elif vr_temps:
            temperature = safe_float(vr_temps[0])
            
        if vr_temps:
            vr_temperature = safe_float(vr_temps[0])
    
    # Backup temperature sources
    if temperature is None and hasattr(data, 'temperature_avg'):
        temperature = safe_float(getattr(data, 'temperature_avg'))
    if temperature is None and hasattr(data, 'env_temp'):
        temperature = safe_float(getattr(data, 'env_temp'))

    # Extract fan speeds
    fans = getattr(data, 'fans', [])
    fan_speeds = []
    if fans:
        for fan in fans:
            if hasattr(fan, 'speed') and fan.speed is not None:
                fan_speeds.append(safe_int(fan.speed))

    # Get pools data
    pools_data = []
    pools = getattr(data, 'pools', [])
    for pool in pools:
        pool_info = {
            "url": str(pool.url) if hasattr(pool, 'url') and pool.url else None,
            "user": pool.user if hasattr(pool, 'user') else None,
            "status": pool.status if hasattr(pool, 'status') else None
        }
        pools_data.append(pool_info)
    
    # If no runtime pools, try config
    if not pools_data:
        config = getattr(data, 'config', None)
        if config and hasattr(config, 'pools') and config.pools:
            pool_config = config.pools
            if hasattr(pool_config, 'groups'):
                for group in pool_config.groups:
                    if hasattr(group, 'pools'):
                        for pool in group.pools:
                            pool_info = {
                                "url": str(pool.url) if hasattr(pool, 'url') and pool.url else None,
                                "user": pool.user if hasattr(pool, 'user') else None,
                                "status": "configured"
                            }
                            pools_data.append(pool_info)

    # Get primary pool name for display
    primary_pool = "No Pool"
    if pools_data and pools_data[0]["url"]:
        try:
            url = pools_data[0]["url"]
            # Extract hostname from URL
            parsed = urllib.parse.urlparse(url if url.startswith(('http', 'stratum')) else f'stratum+tcp://{url}')
            if parsed.hostname:
                primary_pool = parsed.hostname.replace('www.', '').split('.')[0].title()
        except:
            primary_pool = "Unknown Pool"

    normalized = {
        "ip": getattr(data, "ip", None),
        "hostname": getattr(data, "hostname", None),
        "mac": getattr(data, "mac", None),
        "make": getattr(data, "make", None),
        "model": getattr(data, "model", None),
        "firmware": getattr(data, "fw_ver", None),
        
        # Hashrate
        "hashrate_current": safe_float(getattr(data, "raw_hashrate", None).rate if hasattr(data, "raw_hashrate") and getattr(data, "raw_hashrate") else None),
        "hashrate_avg": safe_float(getattr(data, "hashrate", None).rate if hasattr(data, "hashrate") and getattr(data, "hashrate") else None),
        "expected_hashrate": safe_float(getattr(data, "expected_hashrate", None).rate if hasattr(data, "expected_hashrate") and getattr(data, "expected_hashrate") else None),
        
        # Temperature
        "temperature": temperature,
        "temperature_max": temperature_max,
        "vr_temperature": vr_temperature,
        
        # Power & Efficiency
        "power_usage": safe_int(getattr(data, "wattage", None)),
        "power_limit": safe_int(getattr(data, "wattage_limit", None)) if hasattr(data, "wattage_limit") else None,
        "efficiency": safe_float(getattr(data, "efficiency_fract", None)),
        "voltage": safe_float(getattr(data, "voltage", None)) if hasattr(data, "voltage") else None,
        
        # Hardware
        "fan_speeds": fan_speeds,
        "chip_count": safe_int(getattr(data, "total_chips", None)),
        
        # Status
        "is_mining": getattr(data, "is_mining", None),
        "uptime": safe_int(getattr(data, "uptime", None)),
        "errors": getattr(data, "errors", []),
        
        # Pool info
        "pools": pools_data,
        "primary_pool": primary_pool,
        
        # API info
        "api_version": getattr(data, "api_ver", None),
        "timestamp": getattr(data, "timestamp", None),
    }
    
    return normalized

async def get_miner_data_async(ip):
    """Async function to get miner data"""
    try:
        # Get miner data
        miner = await get_miner(ip)
        raw_data = await miner.get_data()
        
        # Normalize the data
        normalized_data = normalize_data(raw_data)
        
        return {
            "success": True,
            "ip": ip,
            "data": normalized_data
        }
        
    except Exception as e:
        return {
            "success": False,
            "error": f"Failed to connect to miner at {ip}: {str(e)}"
        }

def run_async_task(coro):
    """Helper to run async functions in Flask routes"""
    loop = asyncio.new_event_loop()
    asyncio.set_event_loop(loop)
    try:
        return loop.run_until_complete(coro)
    finally:
        loop.close()

@app.route('/api/miners', methods=['GET'])
def get_miner_data():
    ip = request.args.get('ip')
    if not ip:
        return jsonify({"error": "IP parameter is required"}), 400
    
    # Run async function synchronously
    result = run_async_task(get_miner_data_async(ip))
    
    if result["success"]:
        return jsonify(result)
    else:
        return jsonify(result), 500

@app.route('/api/health', methods=['GET'])
def health_check():
    return jsonify({"status": "healthy", "service": "miner-api"})

if __name__ == '__main__':
    print("Starting Miner API Server...")
    print("Available endpoints:")
    print("  GET /api/miners?ip=X.X.X.X - Get miner data")
    print("  GET /api/health - Health check")
    app.run(host='0.0.0.0', port=5001, debug=True)