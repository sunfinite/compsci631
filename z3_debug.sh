#!/bin/bash

rm interaction.txt
tee -a interaction.txt | z3 -in -smt2 | tee -a interaction.txt
