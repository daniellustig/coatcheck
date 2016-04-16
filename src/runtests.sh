#!/bin/bash

# Exit on any errors
set -e

if [ -z "$1" ] || [ -z "$2" ]
then
  echo "Usage: ./runtests.sh <pipeline name> <path to tests> [<output dir>]"
  exit 1
fi

# Store all of the tests in the path tests/x86tso into TESTS
TESTS=$(ls $2 | sed "s/.litmus//")
OUTPUTDIR=results/graphs-$1-$(date +"%m-%d-%y--%H-%M-%S-%p")

if ! [ -z "$3" ]; then
    OUTPUTDIR=$3/$OUTPUTDIR
fi

mkdir -p $OUTPUTDIR
rm -f latest
ln -s $OUTPUTDIR latest

# Loop over each test
date | tee $OUTPUTDIR/$1.log
echo "Test,Num_Graphs,Time,Bugs" >> $OUTPUTDIR/$1.csv
for t in $TESTS
do
  mkdir -p $OUTPUTDIR/$t
  echo Test: $t | tee -a $OUTPUTDIR/$1.log $OUTPUTDIR/$t/$t.log
  # Run the test.
  /usr/bin/time -f "Time: %e seconds" ./pipecheck -i $2/$t.litmus -o $OUTPUTDIR/$t/$t.gv -p $1 2>&1 | tee -a $OUTPUTDIR/$1.log $OUTPUTDIR/$t/$t.log
  wait $!
  # Now pull relevant information from this test's output into the final report
  # and the CSV file.
  grep "Test: " $OUTPUTDIR/$t/$t.log >> $OUTPUTDIR/$1.report
  test_name=$(sed -n "s/Test: \\(.\\+\\)/\\1/p" $OUTPUTDIR/$t/$t.log)
  echo "--------------------" >> $OUTPUTDIR/$1.report
  grep "Total Graphs: " $OUTPUTDIR/$t/$t.log >> $OUTPUTDIR/$1.report
  num_graphs=$(sed -n "s/Total Graphs: \\(.\\+\\)/\\1/p" $OUTPUTDIR/$t/$t.log)
  bugs=""
  # This grep might fail if there are no bugs...
  set +e
  grep "BUG!" $OUTPUTDIR/$t/$t.log >> $OUTPUTDIR/$1.report;
  if [ $? != 0 ]; then
      bugs="No"
  else
      bugs="Yes"
  fi
  set -e
  grep "Time: " $OUTPUTDIR/$t/$t.log >> $OUTPUTDIR/$1.report
  time=$(sed -n "s/Time: \\(.\\+\\) seconds/\\1/p" $OUTPUTDIR/$t/$t.log)
  echo "" >> $OUTPUTDIR/$1.report
  echo "$test_name,$num_graphs,$time,$bugs" >> $OUTPUTDIR/$1.csv
  neato -Tps2 $OUTPUTDIR/$t/$t.gv -o $OUTPUTDIR/$t/$t.ps
  # Only proceed with PDF generation if there's something in the
  # GV and PS files.
  if [ -f $OUTPUTDIR/$t/$t.ps ]; then
      ps2pdf $OUTPUTDIR/$t/$t.ps $OUTPUTDIR/$t/$t.pdf
  fi
  rm -f $OUTPUTDIR/$t/$t.ps
done

wait $!

echo "$0 Done!"
