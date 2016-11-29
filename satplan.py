from encode import *;
from SAT_solver import *;

fh = open(sys.argv[1],'r');    
ThisProblem = problem(fh);
ThisProblem.set_horizon(1);

print(ThisProblem);
print('\tTotal_Statement: %s\n'%( ThisProblem.Total_Statement));

Solver = SAT_solver(ThisProblem.Total_Statement);
Solver.Solve();

print ('%s'%Solver.SAT_problem);
print ('%s'%Solver.Assignments);
print ('Solution:\n%s'%ThisProblem.decode_assignment(Solver.Assignments));

pdb.set_trace();
