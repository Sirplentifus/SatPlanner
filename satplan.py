from encode import *;
from SAT_solver import *;

fh = open(sys.argv[1],'r');    
ThisProblem = problem(fh);
ThisProblem.set_horizon(3);

print(ThisProblem);
print('\tTotal_Statement: %s\n'%( ThisProblem.Total_Statement));

Solver = SAT_solver(ThisProblem.Total_Statement);
Solver.Pre_Simplify();

print ('After pre-simplification: %s'%Solver.SAT_problem);


