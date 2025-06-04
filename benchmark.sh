#!/bin/bash

# Define variables
BINARY="./src/genmc"
ROOT_DIR="./tests/correct/data-structures"
RESULTS_FILE="benchmark_results.csv"

# Clear log file
> "$RESULTS_FILE"

# Loop through all files in the directory
find "$ROOT_DIR" -type d -name "variants" | while read -r VARIANTS_DIR; do
    for FILE in "$VARIANTS_DIR"/*; do
        if [[ -f "$FILE" ]]; then
            echo "Processing $FILE"
            OUTPUT=$("$BINARY" "$FILE" --check-consistency-type=full --check-consistency-point=exec --jam21fullvc 2>&1)

            # Extract values
            EXEC_COUNT=$(echo "$OUTPUT" | grep -oE "Number of complete executions explored: [0-9]+" | awk '{print $6}')
            BLOCKED_COUNT=$(echo "$OUTPUT" | grep -oE "Number of blocked executions seen: [0-9]+" | awk '{print $6}')
            TIME_TAKEN=$(echo "$OUTPUT" | grep -oE "Total wall-clock time: ([0-9.]+)s" | awk '{print $4}')

            # Extract test name and variant
            MAIN_CATEGORY=$(echo "$FILE" | cut -d/ -f4)
            TEST_NAME=$(echo "$FILE" | cut -d/ -f5)
            VARIANT_NAME=$(echo "$FILE" | cut -d/ -f7-)

            # If values are found, append to CSV
            if [[ -n "$EXEC_COUNT" && -n "$TIME_TAKEN" ]]; then
                echo "$MAIN_CATEGORY,$TEST_NAME,$VARIANT_NAME,$EXEC_COUNT,$BLOCKED_COUNT,$TIME_TAKEN" >> "$RESULTS_FILE"
            else
                echo "$MAIN_CATEGORY,$TEST_NAME,$VARIANT_NAME,failed,failed" >> "$RESULTS_FILE"
            fi
        fi
    done
done