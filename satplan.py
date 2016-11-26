from encode import *;

fh = open(sys.argv[1],'r');    
ThisProblem = problem(fh);
ThisProblem.set_horizon(3);

print(ThisProblem);
print('\tTotal_Statement: %s -> %d clauses\n'%(ThisProblem.Total_Statement.Clauses, len(ThisProblem.Total_Statement.Clauses)));
