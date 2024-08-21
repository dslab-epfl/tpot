sum=0
count=5

for value in $(seq 1 $count);
do
    start=`date +%s.%N`
    cn early_alloc.c -I ../original/
    end=`date +%s.%N`
    runtime=$( echo "$end - $start" | bc -l )
    sum=$( echo "$sum + $runtime" | bc -l )
done

echo "$sum / $count" | bc -l
