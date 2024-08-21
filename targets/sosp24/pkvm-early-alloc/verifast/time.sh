sum=0
count=5

make generated.c
for value in $(seq 1 $count);
do
    start=`date +%s.%N`
    verifast -shared -allow_dead_code -link_should_fail generated.c
    end=`date +%s.%N`
    runtime=$( echo "$end - $start" | bc -l )
    sum=$( echo "$sum + $runtime" | bc -l )
done

echo "$sum / $count" | bc -l
