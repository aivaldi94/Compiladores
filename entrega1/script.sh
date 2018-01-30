#!/bin/bash

echo -e "EMPIEZA GOOD \n" >> arch.txt

for (( i=1; i<=60; i++))
	do
		echo -e "\n TEST"$i "\n" >> arch.txt
		./tiger ../tests/good/test$i.tig >> arch.txt
	done

echo -e "EMPIEZA TYPE \n" >> arch.txt

for (( i=1; i<=60; i++))
	do
		echo -e "\n TEST"$i "\n" >> arch.txt
		./tiger ../tests/type/test$i.tig >> arch.txt
	done

