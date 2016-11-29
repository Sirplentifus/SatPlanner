from SAT_defs import *;
import copy;
import pdb;

class SAT_solver:
    def __init__(self, SAT_Problem):
        self.SAT_problem = copy.deepcopy(SAT_Problem);
        self.Assignments = [None]*SAT_Problem.N_Vars;
        self.Pre_Simplify();
        self.Guesses = []; #List of literals representing assignments made in branches
    
    #Applies a version of the DPLL algorithm to solve the problem
    #Returns False if impossible and True if solved
    def Solve(self):
        
        while(True):
            
            print('Current problem complexity: %d'%complexity(self.SAT_problem));
            print('Press enter to continue');
            x = input();
            
            try: 
                self.Simplify();
            except ValueError:
                print('Empty clause found, backtracking...');
                self.BackTrack();
            
            print('Problem complexity after simplification: %d'%complexity(self.SAT_problem));
            if(x=='pp'):
                print(self.SAT_problem);
            
            if(not self.SAT_problem.Clauses):
                print('Problem Solved\n');
                return; #Problem Solved
                
            try:
                if(self.Assign_Units()):
                    continue;
            except ValueError:
                print('Contradicting unit found, backtracking...');
                self.BackTrack();
            
            if(self.Assign_Pure()):
                continue;
            
            #Everything Failed. Branching
            
            #For now the first unassigned literal is chosen, but later
            #the one that appears the most (?) will be chosen
            
            new_guess = Guess();
            new_guess.Sentence_Before = copy.deepcopy(self.SAT_problem);
            
            for i in range(self.SAT_problem.N_Vars):
                if(self.Assignments[i] == None):
                    new_guess.Lit_ID = i;
                    new_guess.Tried[True] = True;
                    self.Assignments[i] = True;
                    break;
            self.Guesses.append(new_guess);
            print('No units or literals found - branching: %s'%new_guess);
            print('Full tree:%s'%self.Guesses);
            
    
    #Removes clauses with true literals
    #Removes literals that are false
    #Raises exception if clauses are empty
    def Simplify(self):
        
        rem_clauses = [];
        for Clause in self.SAT_problem.Clauses:
            rem_lits = [];
            for lit in Clause:
                if(self.Assignments[lit.ID] == None):
                    continue;
                if(lit.Affirm == self.Assignments[lit.ID]):
                    rem_clauses.append(Clause);
                    rem_lits = [];
                    break;
                if(lit.Affirm != self.Assignments[lit.ID]):
                    rem_lits.append(lit);
            for rem_lit in rem_lits:
                Clause.remove(rem_lit);
            if(not Clause):
                raise(ValueError('Empty Clause produced by simplify'));
        
        for rem_clause in rem_clauses:
            self.SAT_problem.Clauses.remove(rem_clause);
            
        
    #Removes contradicting literals in a clause
    #Removes repeating literals in a clause
    #Returns True if problem was found to be impossible, and False otherwise
    #Only needs to be ran once
    #Of all the times it was used, it did nothing, however it is kept
    #because it guarantees that each clause only has one of each kind
    #of literals
    def Pre_Simplify(self): 
        for Clause in self.SAT_problem.Clauses:
            
            finished = False;
            while(not finished):
                finished = True;
                for lit in Clause:
                    eq_lits = [x for x in Clause if x.ID == lit.ID and (not x is lit)];
                    
                    if(eq_lits):
                        finished = False;
                        pdb.set_trace();
                        
                    delete_all_eqs = False;
                    for eq_lit in eq_lits:
                        if(eq_lit.Affirm != lit.Affirm):
                            delete_all_eqs = True;
                            break;
                    
                    for eq_lit in eq_lits:
                        Clause.remove(eq_lit);
                    
                    if(delete_all_eqs):
                        Clause.remove(lit);
                
            if(not Clause):
                raise(ValueError('Simplification produces empty clause'));
                        
    #Assign all the literals in unit clauses.
    #Raises exception if an assignment contradicts an existing one
    #Returns True if any units were found and False otherwise
    def Assign_Units(self):
        ret = False;
        Clauses_to_Remove = [];
        for Clause in self.SAT_problem.Clauses:
            if(len(Clause) == 1):
                ret = True;
                unit_lit = Clause[0];
                if(self.Assignments[unit_lit.ID] == (not unit_lit.Affirm)): #WARNING: not None evalueates to True
                    raise(ValueError('Unit assignment contradicts previous assignment'));
                self.Assignments[unit_lit.ID] = unit_lit.Affirm;
                Clauses_to_Remove.append(Clause);
        if(Clauses_to_Remove):
            print('Unit clauses found: %s'%Clauses_to_Remove);
        for Clause_to_Remove in Clauses_to_Remove:
            self.SAT_problem.Clauses.remove(Clause_to_Remove);
        return ret;

    #Look for pure symbols and assign the one that appears in the most clauses
    def Assign_Pure(self):
        Literals = [Literal_Info() for i in range(self.SAT_problem.N_Vars)];
        
        for Clause in self.SAT_problem.Clauses:
            for lit in Clause:
                if(Literals[lit.ID].PureAffirm==None):
                    Literals[lit.ID].PureAffirm = lit.Affirm;
                    Literals[lit.ID].N_Appear += 1;
                    continue;
                if(Literals[lit.ID].N_Appear < 0):
                    continue;
                if(lit.Affirm == Literals[lit.ID].PureAffirm):
                    Literals[lit.ID].N_Appear += 1;
                else:
                    Literals[lit.ID].N_Appear = -1;
        
        ID = max(range(self.SAT_problem.N_Vars), key = lambda ind: Literals[ind].N_Appear);
        
        if( Literals[ID].N_Appear > 0):
            self.Assignments[ID] = Literals[ID].PureAffirm;
            print('Pure iteral found: %s'%Literal(ID ,Literals[ID].PureAffirm));
            return True;
        else:
            return False;
    
    #Backs up until the last guess that still has an untried option
    def BackTrack(self):
        while(self.Guesses):
            this_Guess = self.Guesses.pop();
            Untried = [a for a in this_Guess.Tried if this_Guess.Tried[a]==False];
            if(Untried):
                Untried = Untried[0];
                this_Guess.Tried[Untried] = True;
                self.Assignments[this_Guess.Lit_ID] = bool(Untried);
                self.SAT_Problem = this_Guess.Sentence_Before;
                self.Guesses.append(this_Guess);
                print('Guesses list: %s'%self.Guesses);
                return;
            else:
                self.Assignments[this_Guess.Lit_ID] = None;
                continue;
        
            
        raise(ValueError('Problem is impossible'));
        
        
    
#Useful class to keep general info on the literals
class Literal_Info:
    N_Appear = 0; #Num of clauses it appears in. Negative if impure
    PureAffirm = None; #This pure literal has which affirm
    
    #For debugging:
    def __repr__(self):
        if(self.N_Appear < 0):
            return '<Impure>';
        else:    
            return '<%s,%d>'%(self.PureAffirm, self.N_Appear);

#Class that maintains info on guesses made
class Guess:
    Lit_ID = -1;
    Tried = [False]*2;
    Sentence_Before = SAT_Sentence();
    
    #For debugging:
    def __repr__(self):
        return '<%d, %s>'%(self.Lit_ID, self.Tried);
    
    
