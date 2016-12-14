 _______  _______ _________ _______  _        _______  _       
(  ____ \(  ___  )\__   __/(  ____ )( \      (  ___  )( (    /|
| (    \/| (   ) |   ) (   | (    )|| (      | (   ) ||  \  ( |
| (_____ | (___) |   | |   | (____)|| |      | (___) ||   \ | |
(_____  )|  ___  |   | |   |  _____)| |      |  ___  || (\ \) |
      ) || (   ) |   | |   | (      | |      | (   ) || | \   |
/\____) || )   ( |   | |   | )      | (____/\| )   ( || )  \  |
\_______)|/     \|   )_(   |/       (_______/|/     \||/    )_)


===Made by===
Simão Marto		    nº75326
Eric Loewenthal		nº75848 


===Usage===

run the following command:

~# python3 satplan.py <file_name>

e.g.: 
~# python3 satplan.py Tests/blocks6.dat

In this folder, you should be able to find, inside folder Tests, a series of test files that our program can solve.
The slowest one, iter2.dat, is solved in about 4 minutes (on our machine). iter3.dat, unfortunately, cannot be solved
in reasonable time (it takes 3 hours and 20 minutes), and thus was not included.

As an alternative, all tests in folder Tests can be run sequentially with basic timing using:

~# python3 Run_Tests.py

This script will run all available tests and separately time the initial encoding and solution stages.
Solution times include the time needed to compile the encoded problem for the specific horizon and include
*all* horizon steps, from h=1 until a solution is found or the limit is reached. 

Note:
    By default, the VSIDS solver is used. This can be changed by editing the scripts to reflect the
    desired solver. VSIDS is orders of magnitude faster than the basic DPLL solver and is thus the default.

    
===Systems with only Python 3.x installed===

If Python 2 is not present on your system, you may need to run the above commands with

~# python 

instead of 

~# python3


===Files===

encoder.py
	File with all the code relevant to reading the PDLL problem and encoding it in SAT
Quine_McCluskey_nary.py
	Implements an algorithm to simplify clauses based on the Quine-McCluskey algorithm
SAT_solver.py
	Code to solve the SAT problem with no heuristics
SAT_solver_heur.py
	Code to solve the SAT problem with a simple heuristic
SAT_solver_VSIDS.py
	Code to solve the SAT problem with a better heuristic
satplan.py
	Code that combines the encoder with a solver to obtain a solution to a problem
Run_Tests.py
    Code to run all test files in folder Tests and time them