from flask import Flask, request, jsonify
from flask_cors import CORS
import asyncio
from pyasic import get_miner
import logging

app = Flask(__name__)
CORS(app)

# Configure logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

async def get_miner_data(ip):
    """Async function to get miner data using pyasic"""
    try:
        miner = await get_miner(ip)
        if miner is None:
            return None, f"Could not connect to miner at {ip}"
        
        # Get miner data
        data = await miner.get_data()
        miner_dict = data.as_dict()

        print("\n=== RAW MINER DATA ===")
        print(miner_dict)  
        print("======================\n")
        
        # Add some debugging info
        logger.info(f"Successfully connected to miner at {ip}")
        logger.info(f"Miner type: {type(miner)}")
        logger.info(f"Available data keys: {list(miner_dict.keys())}")
        
        return miner_dict, None
        
    except Exception as e:
        logger.error(f"Error getting miner data from {ip}: {str(e)}")
        return None, str(e)

@app.route('/api/miners', methods=['GET'])
def get_miners():
    ip = request.args.get('ip')
    
    if not ip:
        return jsonify({'error': 'Miner IP address is required'}), 400
    
    try:
        # Run the async function
        loop = asyncio.new_event_loop()
        asyncio.set_event_loop(loop)
        data, error = loop.run_until_complete(get_miner_data(ip))
        loop.close()
        
        if error:
            return jsonify({'error': error}), 500
            
        if data is None:
            return jsonify({'error': f'Could not connect to miner at {ip}'}), 500
        
        return jsonify(data)
        
    except Exception as e:
        logger.error(f"Unexpected error: {str(e)}")
        return jsonify({'error': f'Unexpected error: {str(e)}'}), 500

@app.route('/health', methods=['GET'])
def health_check():
    return jsonify({'status': 'healthy', 'service': 'pyasic-miner-api'})

if __name__ == '__main__':
    print("Starting pyasic miner API on http://localhost:5001")
    app.run(host='0.0.0.0', port=5001, debug=True)