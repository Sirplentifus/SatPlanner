from SAT_defs import *;
import copy;

class SAT_solver:
    def __init__(self, SAT_Problem):
        self.SAT_problem = copy.deepcopy(SAT_Problem);
        self.Assignments = [None]*SAT_Problem.N_Vars;
        self.Pre_Simplify();
    
    #Removes clauses with true literals, and literals that are false
    #Raises exception if clauses are empty
    def Simplify(self):
        pass;
    
    #DOESN'T APPEAR TO BE USEFUL
    #Removes contradicting literals in a clause
    #Removes repeating literals in a clause
    #Raises exception if clauses are empty
    def Pre_Simplify(self): 
        for Clause in self.SAT_problem.Clauses:
            for lit in Clause:
                if( lit.Affirm == self.Assignments[lit.ID] ):
                    #Literal returns true for current assignment
                    self.SAT_problem.Clauses.remove(Clause);
                    pdb.set_trace();
                if( lit.Affirm == self.Assignments[lit.ID] ):
                    #Literal returns true in terms of assignment
                    Clause.remove(lit);
                    pdb.set_trace();
                
            if(not Clause):
                raise(ValueError('Simplification produces empty clause'));
                    
        
    #Applies a version of the DPLL algorithm to solve the problem
    def Solve(self):
        pass;
