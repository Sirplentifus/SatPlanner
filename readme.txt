 _______  _______ _________ _______  _        _______  _       
(  ____ \(  ___  )\__   __/(  ____ )( \      (  ___  )( (    /|
| (    \/| (   ) |   ) (   | (    )|| (      | (   ) ||  \  ( |
| (_____ | (___) |   | |   | (____)|| |      | (___) ||   \ | |
(_____  )|  ___  |   | |   |  _____)| |      |  ___  || (\ \) |
      ) || (   ) |   | |   | (      | |      | (   ) || | \   |
/\____) || )   ( |   | |   | )      | (____/\| )   ( || )  \  |
\_______)|/     \|   )_(   |/       (_______/|/     \||/    )_)
                                                                                                                              

===Made by===
Eric Loewenthal		nº75848 
Simão Marto		nº75326

===Usage===

run the following command:

$ python3 satplan.py <file_name>

e.g.: 
$ python3 satplan.py Tests/blocks6.dat

In this folder, you should be able to find, inside folder Tests, a series of test files that our program can solve.
The slowest one, iter2.dat, is solved in about 4 minutes (in our machine). iter3.dat, unfortunately, cannot be solved
in due time, and thus was not included.

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
