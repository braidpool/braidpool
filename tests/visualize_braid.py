#!/usr/bin/env python
"""
Braid Visualization Tool

This script loads a braid structure from a JSON file and visualizes it,
saving the result to a PNG file.
"""

import os
import sys
import argparse
from simulator import Braid
import matplotlib.pyplot as plt

def main():
    # Set up argument parser
    parser = argparse.ArgumentParser(description='Visualize a braid structure from a JSON file')
    parser.add_argument('input_file', help='Path to the braid JSON file to visualize')
    parser.add_argument('-o', '--output', help='Path to save the output PNG file (default: <input_file_name>.png)')
    args = parser.parse_args()
    
    # Check if input file exists
    if not os.path.exists(args.input_file):
        print(f"❌ Error: Input file {args.input_file} does not exist")
        return 1
    
    # Set default output file if not specified
    if not args.output:
        input_name = os.path.splitext(os.path.basename(args.input_file))[0]
        args.output = f"{input_name}.png"
    
    try:
        # Load and visualize the braid
        print(f"🔍 Loading braid from {args.input_file}...")
        braid = Braid(filename=args.input_file)
        
        print(f"📊 Visualizing braid structure...")
        print(f"   - Number of beads: {len(braid.beads)}")
        print(f"   - Number of cohorts: {len(braid.cohorts)}")
        print(f"   - Number of tips: {len(braid.tips)}")
        
        # Plot and save
        braid.plot(filename=args.output)
        print(f"✅ Visualization saved to {args.output}")
        return 0
    except Exception as e:
        print(f"❌ Error: {str(e)}")
        return 1

if __name__ == "__main__":
    sys.exit(main()) 