#!/bin/bash

# Usage message
if [ $# -lt 1 ]; then
    echo "Usage: $0 <PID>"
    exit 1
fi

# Process ID (PID) of the process you want to monitor
PID=$1

# Output CSV file
OUTPUT_FILE="process_usage_log.csv"

# Header for CSV file
echo "timestamp,PID,CPU%,VmSize_kB,VmRSS_kB,VmData_kB,VmStk_kB" > "$OUTPUT_FILE"

# Check if the process exists
if ! ps -p $PID > /dev/null; then
    echo "Process with PID $PID not found. Please provide a valid PID."
    exit 1
fi

# Monitor the process every second
while ps -p $PID > /dev/null; do
    TIMESTAMP=$(date "+%Y-%m-%d %H:%M:%S")
    
    # Get the CPU usage (in percentage)
    CPU_USAGE=$(ps -p $PID -o %cpu=)
    
    # Get the memory usage (VmSize, VmRSS, VmData, VmStk)
    STATUS_FILE="/proc/$PID/status"
    
    VMSIZE=$(grep VmSize "$STATUS_FILE" | awk '{print $2}')
    VMRSS=$(grep VmRSS "$STATUS_FILE" | awk '{print $2}')
    VMDATA=$(grep VmData "$STATUS_FILE" | awk '{print $2}')
    VMSTK=$(grep VmStk "$STATUS_FILE" | awk '{print $2}')
    
    # Save the data to the CSV file
    echo "$TIMESTAMP,$PID,$CPU_USAGE,$VMSIZE,$VMRSS,$VMDATA,$VMSTK" >> "$OUTPUT_FILE"
    
    # Sleep for 1 second before the next update
    sleep 1
done

echo "Process $PID has ended. Data saved to $OUTPUT_FILE."
