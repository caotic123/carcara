
#!/bin/bash

# Check if a command was provided
if [ $# -eq 0 ]; then
  echo "Usage: $0 <command>"
  exit 1
fi

# The command to benchmark
CMD="$@"

# Array to store execution times
declare -a TIMES

# Run the command 100 times and measure execution time
echo "Running '$CMD' 100 times..."
for i in {1..100}; do
  # Measure time with millisecond precision
  START=$(date +%s.%N)
  $CMD > /dev/null 2>&1
  END=$(date +%s.%N)
  
  # Calculate execution time
  TIME=$(echo "$END - $START" | bc)
  
  # Store the time
  TIMES+=($TIME)
  
  # Show progress
  echo -ne "Progress: $i/100\r"
done
echo -e "Progress: 100/100"

# Sort the times
SORTED_TIMES=($(printf "%s\n" "${TIMES[@]}" | sort -n))

# Calculate median
ARRAY_LENGTH=${#SORTED_TIMES[@]}
if [ $((ARRAY_LENGTH % 2)) -eq 0 ]; then
  # Even number of elements
  MID1=${SORTED_TIMES[$((ARRAY_LENGTH / 2 - 1))]}
  MID2=${SORTED_TIMES[$((ARRAY_LENGTH / 2))]}
  MEDIAN=$(echo "scale=6; ($MID1 + $MID2) / 2" | bc)
else
  # Odd number of elements
  MEDIAN=${SORTED_TIMES[$((ARRAY_LENGTH / 2))]}
fi

echo "Median execution time: $MEDIAN seconds"