#!/bin/bash

convert_seconds_to_min_sec() {
    local T=$1
    if [ $T -lt 60 ]; then
        echo "$T""s"
        return
    fi
    local M=$((T/60))
    local S=$((T%60))
    echo "$M""m:""$S""s"
}

measure_setup_time() {
    start=$(date +%s)
    cd ../..
    make --file=Makefile.common clean-tpot > /dev/null 2>&1
    make --file=Makefile.common -j$(nproc) tpot > /dev/null 2>&1
    rm -rf ~/dl/solver-portfolio
    portfolio/setup-portfolio.sh ~/dl/solver-portfolio sosp24 > /dev/null 2>&1
    cd targets/sosp24
    end=$(date +%s)
    echo $((end-start))
}

echo "This script will delete the default cache located at ~/z3_cache"
read -p "(Press Enter to continue ...)"

TMP_LOG=/tmp/pot_log

echo "Measuring setup time ..."
SETUP_TIME=$(measure_setup_time)
echo "Setup time: $(convert_seconds_to_min_sec $SETUP_TIME)"
echo "Running POTs..."
echo ""

echo "pKVM emem allocator"
echo "----------------------------------------------------------------------------"
printf "%-15s %-10s %-10s %-10s %-15s %-10s\n" "# of POTs" "Avg" "Min" "Max" "CI time" "CPU time"
echo "----------------------------------------------------------------------------"
cd pkvm-early-alloc/tpot

start=$(date +%s)   
make verify-all > $TMP_LOG 2>/dev/null
end=$(date +%s)
PARALLEL_TIME=$((end-start))

NO_POTS=$(grep -E "POT .* passed in [0-9]+ secs" $TMP_LOG | wc -l)
AVG=$(grep -E "POT .* passed in [0-9]+ secs" $TMP_LOG | awk '{print $5}' | awk '{s+=$1} END {print int(s/NR)}')
MIN=$(grep -E "POT .* passed in [0-9]+ secs" $TMP_LOG | awk '{print $5}' | sort -n | head -n 1)
MAX=$(grep -E "POT .* passed in [0-9]+ secs" $TMP_LOG | awk '{print $5}' | sort -n | tail -n 1)
CI_TIME=$((SETUP_TIME + PARALLEL_TIME))
CPU_TIME=$(grep -E "POT .* passed in [0-9]+ secs" $TMP_LOG | awk '{print $5}' | awk '{s+=$1} END {print s}')
cd ../..
printf "%-15s %-10s %-10s %-10s %-15s %-10s\n" $NO_POTS $(convert_seconds_to_min_sec $AVG) $(convert_seconds_to_min_sec $MIN) $(convert_seconds_to_min_sec $MAX) $(convert_seconds_to_min_sec $CI_TIME) $(convert_seconds_to_min_sec $CPU_TIME)
echo "----------------------------------------------------------------------------"
echo ""


echo "Vigor allocator"
echo "----------------------------------------------------------------------------"
printf "%-15s %-10s %-10s %-10s %-15s %-10s\n" "# of POTs" "Avg" "Min" "Max" "CI time" "CPU time"
echo "----------------------------------------------------------------------------"
cd klint/tpot-specs/index_pool

start=$(date +%s)   
make verify-all > $TMP_LOG 2>/dev/null
end=$(date +%s)
PARALLEL_TIME=$((end-start))

NO_POTS=$(grep -E "POT .* passed in [0-9]+ secs" $TMP_LOG | wc -l)
AVG=$(grep -E "POT .* passed in [0-9]+ secs" $TMP_LOG | awk '{print $5}' | awk '{s+=$1} END {print int(s/NR)}')
MIN=$(grep -E "POT .* passed in [0-9]+ secs" $TMP_LOG | awk '{print $5}' | sort -n | head -n 1)
MAX=$(grep -E "POT .* passed in [0-9]+ secs" $TMP_LOG | awk '{print $5}' | sort -n | tail -n 1)
CI_TIME=$((SETUP_TIME + PARALLEL_TIME))
CPU_TIME=$(grep -E "POT .* passed in [0-9]+ secs" $TMP_LOG | awk '{print $5}' | awk '{s+=$1} END {print s}')
cd ../../..
printf "%-15s %-10s %-10s %-10s %-15s %-10s\n" $NO_POTS $(convert_seconds_to_min_sec $AVG) $(convert_seconds_to_min_sec $MIN) $(convert_seconds_to_min_sec $MAX) $(convert_seconds_to_min_sec $CI_TIME) $(convert_seconds_to_min_sec $CPU_TIME)
echo "----------------------------------------------------------------------------"
echo ""

echo "KVM page table"
echo "----------------------------------------------------------------------------"
printf "%-15s %-10s %-10s %-10s %-15s %-10s\n" "# of POTs" "Avg" "Min" "Max" "CI time" "CPU time"
echo "----------------------------------------------------------------------------"
cd kvm-pgtable

start=$(date +%s)   
make verify-all > $TMP_LOG 2>/dev/null
end=$(date +%s)
PARALLEL_TIME=$((end-start))

NO_POTS=$(grep -E "POT .* passed in [0-9]+ secs" $TMP_LOG | wc -l)
AVG=$(grep -E "POT .* passed in [0-9]+ secs" $TMP_LOG | awk '{print $5}' | awk '{s+=$1} END {print int(s/NR)}')
MIN=$(grep -E "POT .* passed in [0-9]+ secs" $TMP_LOG | awk '{print $5}' | sort -n | head -n 1)
MAX=$(grep -E "POT .* passed in [0-9]+ secs" $TMP_LOG | awk '{print $5}' | sort -n | tail -n 1)
CI_TIME=$((SETUP_TIME + PARALLEL_TIME))
CPU_TIME=$(grep -E "POT .* passed in [0-9]+ secs" $TMP_LOG | awk '{print $5}' | awk '{s+=$1} END {print s}')
cd ..
printf "%-15s %-10s %-10s %-10s %-15s %-10s\n" $NO_POTS $(convert_seconds_to_min_sec $AVG) $(convert_seconds_to_min_sec $MIN) $(convert_seconds_to_min_sec $MAX) $(convert_seconds_to_min_sec $CI_TIME) $(convert_seconds_to_min_sec $CPU_TIME)
echo "----------------------------------------------------------------------------"
echo ""

echo "USB driver"
echo "----------------------------------------------------------------------------"
printf "%-15s %-10s %-10s %-10s %-15s %-10s\n" "# of POTs" "Avg" "Min" "Max" "CI time" "CPU time"
echo "----------------------------------------------------------------------------"
cd usbmouse

start=$(date +%s)   
make verify-all > $TMP_LOG 2>/dev/null
end=$(date +%s)
PARALLEL_TIME=$((end-start))

NO_POTS=$(grep -E "POT .* passed in [0-9]+ secs" $TMP_LOG | wc -l)
AVG=$(grep -E "POT .* passed in [0-9]+ secs" $TMP_LOG | awk '{print $5}' | awk '{s+=$1} END {print int(s/NR)}')
MIN=$(grep -E "POT .* passed in [0-9]+ secs" $TMP_LOG | awk '{print $5}' | sort -n | head -n 1)
MAX=$(grep -E "POT .* passed in [0-9]+ secs" $TMP_LOG | awk '{print $5}' | sort -n | tail -n 1)
CI_TIME=$((SETUP_TIME + PARALLEL_TIME))
CPU_TIME=$(grep -E "POT .* passed in [0-9]+ secs" $TMP_LOG | awk '{print $5}' | awk '{s+=$1} END {print s}')
cd ..
printf "%-15s %-10s %-10s %-10s %-15s %-10s\n" $NO_POTS $(convert_seconds_to_min_sec $AVG) $(convert_seconds_to_min_sec $MIN) $(convert_seconds_to_min_sec $MAX) $(convert_seconds_to_min_sec $CI_TIME) $(convert_seconds_to_min_sec $CPU_TIME)
echo "----------------------------------------------------------------------------"
echo ""

echo "Komodo-S"
echo "----------------------------------------------------------------------------"
printf "%-15s %-10s %-10s %-10s %-15s %-10s\n" "# of POTs" "Avg" "Min" "Max" "CI time" "CPU time"
echo "----------------------------------------------------------------------------"
cd komodo-serval

start=$(date +%s)   
make verify-all > $TMP_LOG 2>/dev/null
end=$(date +%s)
PARALLEL_TIME=$((end-start))

NO_POTS=$(grep -E "POT .* passed in [0-9]+ secs" $TMP_LOG | wc -l)
AVG=$(grep -E "POT .* passed in [0-9]+ secs" $TMP_LOG | awk '{print $5}' | awk '{s+=$1} END {print int(s/NR)}')
MIN=$(grep -E "POT .* passed in [0-9]+ secs" $TMP_LOG | awk '{print $5}' | sort -n | head -n 1)
MAX=$(grep -E "POT .* passed in [0-9]+ secs" $TMP_LOG | awk '{print $5}' | sort -n | tail -n 1)
CI_TIME=$((SETUP_TIME + PARALLEL_TIME))
CPU_TIME=$(grep -E "POT .* passed in [0-9]+ secs" $TMP_LOG | awk '{print $5}' | awk '{s+=$1} END {print s}')
cd ..
printf "%-15s %-10s %-10s %-10s %-15s %-10s\n" $NO_POTS $(convert_seconds_to_min_sec $AVG) $(convert_seconds_to_min_sec $MIN) $(convert_seconds_to_min_sec $MAX) $(convert_seconds_to_min_sec $CI_TIME) $(convert_seconds_to_min_sec $CPU_TIME)
echo "----------------------------------------------------------------------------"
echo ""

echo "Komodo-*"
echo "----------------------------------------------------------------------------"
printf "%-15s %-10s %-10s %-10s %-15s %-10s\n" "# of POTs" "Avg" "Min" "Max" "CI time" "CPU time"
echo "----------------------------------------------------------------------------"
cd komodo-star

start=$(date +%s)   
make verify-all > $TMP_LOG 2>/dev/null
end=$(date +%s)
PARALLEL_TIME=$((end-start))

NO_POTS=$(grep -E "POT .* passed in [0-9]+ secs" $TMP_LOG | wc -l)
AVG=$(grep -E "POT .* passed in [0-9]+ secs" $TMP_LOG | awk '{print $5}' | awk '{s+=$1} END {print int(s/NR)}')
MIN=$(grep -E "POT .* passed in [0-9]+ secs" $TMP_LOG | awk '{print $5}' | sort -n | head -n 1)
MAX=$(grep -E "POT .* passed in [0-9]+ secs" $TMP_LOG | awk '{print $5}' | sort -n | tail -n 1)
CI_TIME=$((SETUP_TIME + PARALLEL_TIME))
CPU_TIME=$(grep -E "POT .* passed in [0-9]+ secs" $TMP_LOG | awk '{print $5}' | awk '{s+=$1} END {print s}')
cd ..
printf "%-15s %-10s %-10s %-10s %-15s %-10s\n" $NO_POTS $(convert_seconds_to_min_sec $AVG) $(convert_seconds_to_min_sec $MIN) $(convert_seconds_to_min_sec $MAX) $(convert_seconds_to_min_sec $CI_TIME) $(convert_seconds_to_min_sec $CPU_TIME)
echo "----------------------------------------------------------------------------"
echo ""

rm -f $TMP_LOG