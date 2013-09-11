#!/bin/sh

# Run testcases for lemma filter only
# This below command is very useful (just REMEMBER to design testcases BEFORE coding)

. ./setupenv

{ 
while true; do
	sbt "test-only leon.test.solvers.lemmafilter.*"
	echo "[info] Sleep in two minutes and then wake up!"
	sleep 120
done
}  >> log.txt &
