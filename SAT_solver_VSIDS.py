from SAT_defs import *
import copy
import pdb
import random


class SAT_solver:
    def __init__(self, CNF_SAT_Problem):
        self.CNF_SAT_Problem = CNF_SAT_Problem

        #  learned_clause keeps track of the last learned clause
        self.learned_clause = []
        self.Assignments = [None]*CNF_SAT_Problem.N_Vars

        self.Guesses = []  # List of literals representing assignments made in branches
        self.DEBUG = False
        self.ASK = False

        self.Unsolvable = False

        self.Pre_Simplify()

        self.nvars = self.CNF_SAT_Problem.N_Vars

        # We don't need to calculate the heuristic on every branch,
        # just update it
        self.persistent_heuristic = [0]*self.CNF_SAT_Problem.N_Vars

        # Tunables
        self.DEBUG = False
        self.ASK = False
        self.NEW_CLAUSE_WEIGHT = 0.05  # New clauses are weighted by 1+x% more than old ones
        self.INIT_HEUR = 0.0009765625  # We start low to better use a float's dynamic range
        self.LIMIT_LEARN_CLAUSE_LEN = True  # Significant speedups
        self.MAX_LEARN_CLAUSE_LEN = 4  # 4 seems optimal
        self.TRY_RANDOM_CHOICE = False  # Does not seem to help currently
        self.RANDOM_CHOICE_LKHD = 2     # Given in units compatible with the range
        self.RANDOM_RANGE_START = 1
        self.RANDOM_RANGE_END   = 100

        # Tunable init
        self.curr_heur_val = self.INIT_HEUR
        self.heur_factor = 1 + self.NEW_CLAUSE_WEIGHT

        self.Init_Heur()

    # Applies a version of the DPLL algorithm to solve the problem
    # Returns False if impossible and True if solved
    def Solve(self):

       
            
        while True:

            if self.DEBUG:
                print('Current problem complexity: %d'%complexity(self.CNF_SAT_Problem))
                if self.ASK:
                    print('Press enter to continue')
                    x = input()
                else:
                    x = ''
                    print()

            if not self.Simplify():
                if not self.Guesses:  # Kore de saigo da (This ends here)
                    return False
                if self.DEBUG:
                    print('Assignment is inconsistent, backtracking...')
                if self.BackTrack():
                    continue
                else:
                    return False
            if self.DEBUG:
                print('Problem complexity after simplification: %d'%complexity(self.CNF_SAT_Problem))
                if 'p' in x:
                    print(self.CNF_SAT_Problem)
                if 'a' in x:
                    ass_print(self.Assignments)
                # if('c' in x):
                #    self.DEBUG = False;
                if 'n' in x:
                    self.ASK = False
                # if('d' in x):
                if 'c' in x:
                    pdb.set_trace()

            if not self.CNF_SAT_Problem.Clauses:
                return True  # Problem Solved

            if self.Assign_Units():
                continue

            if self.Assign_Pure():
                continue

            # Everything Failed. Branching

            # At this point, the heuristic is updated and used to determine the guess to make
            #
            #   We're currently using a VSIDS, described below

            new_guess = Guess()
            new_guess.Sentence_Before = copy.copy(self.CNF_SAT_Problem)
            new_guess.Assignments_Before = copy.copy(self.Assignments)

            # Update heuristic
            chosen_lit = self.Update_Heur()

            if(self.DEBUG):
                print('Heuristic: %s'%[h for h in self.persistent_heuristic])

            if (self.Assignments[chosen_lit] == None):
                new_guess.Lit_ID = chosen_lit
                new_guess.Tried[False] = True
                self.Assignments[chosen_lit] = False

            else:
                # This really shouldn't happen
                raise(ValueError("Tried to assign to already-assigned literal!"))


            # Find the first unassigned
            #for i in range(self.CNF_SAT_Problem.N_Vars):
                # if(self.Assignments[i] == None):
                    # new_guess.Lit_ID = i;
                    # new_guess.Tried[False] = True;
                    # self.Assignments[i] = False;
                    # break;

            self.Guesses.append(new_guess)
            if(self.DEBUG):
                print('No units or literals found - branching: %s'%new_guess)
                print('Full tree:%s'%self.Guesses)

    # Removes clauses with true literals
    # Removes literals that are false
    # Returns False if problem is unsolvable, and True otherwise
    def Simplify(self):

        if(self.Unsolvable):
            return False

        rem_clauses = []
        for Clause in self.CNF_SAT_Problem.Clauses:
            rem_lits = []
            for lit in Clause:
                if(self.Assignments[lit.ID] == None):
                    continue
                if(lit.Affirm == self.Assignments[lit.ID]):
                    rem_clauses.append(Clause)
                    rem_lits = []
                    break
                if(lit.Affirm != self.Assignments[lit.ID]):
                    rem_lits.append(lit)
            for rem_lit in rem_lits:
                Clause.remove(rem_lit)
            if(not Clause):
                return False

        for rem_clause in rem_clauses:
            self.CNF_SAT_Problem.Clauses.remove(rem_clause)
        return True

    # Removes contradicting literals in a clause
    # Removes repeating literals in a clause
    # Returns True if problem was found to be impossible, and False otherwise
    # Only needs to be ran once
    # Of all the times it was used, it did nothing, however it is kept
    # because it guarantees that each clause only has one of each kind
    # of literals
    def Pre_Simplify(self):
        for Clause in self.CNF_SAT_Problem.Clauses:

            finished = False
            while(not finished):
                finished = True
                for lit in Clause:
                    eq_lits = [x for x in Clause if x.ID == lit.ID and (not x is lit)]

                    if(eq_lits):
                        finished = False

                    delete_all_eqs = False
                    for eq_lit in eq_lits:
                        if(eq_lit.Affirm != lit.Affirm):
                            delete_all_eqs = True
                            break

                    for eq_lit in eq_lits:
                        Clause.remove(eq_lit)

                    if(delete_all_eqs):
                        Clause.remove(lit)

            if(not Clause):
                self.Unsolvable = True
                return

    # Assign all the literals in unit clauses.
    # Returns True if any units were found or problem was found to be
    # unsolvable and False otherwise
    # If it finds the problem unsolvable, it sets the flag Unsolvable
    def Assign_Units(self):
        ret = False
        Clauses_to_Remove = []
        for Clause in self.CNF_SAT_Problem.Clauses:
            if(len(Clause) == 1):
                ret = True
                unit_lit = Clause[0]
                if(self.Assignments[unit_lit.ID] == (not unit_lit.Affirm)):  # WARNING: not None evaluates to True
                    self.Unsolvable = True
                    return True
                self.Assignments[unit_lit.ID] = unit_lit.Affirm
                Clauses_to_Remove.append(Clause)
        if(self.DEBUG and bool(Clauses_to_Remove)):
            print('Unit clauses found: %s'%Clauses_to_Remove)
        for Clause_to_Remove in Clauses_to_Remove:
            self.CNF_SAT_Problem.Clauses.remove(Clause_to_Remove)
        return ret

    # Look for pure symbols and assign them
    #
    #   Returns false if no pure symbols are found
    def Assign_Pure(self):
        Literals = [Literal_Info() for i in range(self.CNF_SAT_Problem.N_Vars)]

        for Clause in self.CNF_SAT_Problem.Clauses:
            for lit in Clause:
                if(Literals[lit.ID].PureAffirm == None):
                    Literals[lit.ID].PureAffirm = lit.Affirm
                    Literals[lit.ID].N_Appear += 1
                    continue
                if(Literals[lit.ID].N_Appear < 0):
                    continue
                if(lit.Affirm == Literals[lit.ID].PureAffirm):
                    Literals[lit.ID].N_Appear += 1
                else:
                    Literals[lit.ID].N_Appear = -1

        ret = False
        for ind in range(self.CNF_SAT_Problem.N_Vars):
            if(Literals[ind].N_Appear > 0):
                self.Assignments[ind] = Literals[ind].PureAffirm
                ret = True

        if(self.DEBUG and ret):
            S = 'Pure literals found: '
            for ind in range(self.CNF_SAT_Problem.N_Vars):
                if(Literals[ind].N_Appear > 0):
                    S += '%s '%Literal(ind, Literals[ind].PureAffirm)
            print(S)

        return ret

    # Calculate the initial heuristic for the problem
    #
    # Very similar to the update, minus some details
    #
    #   No return
    def Init_Heur(self):
        # We're using a modified VSIDS heuristic:
        #   The number of clauses a variable appears in is counted.
        #   These counts are updated whenever clauses are learned.
        #   Newly-learned clauses are weighted with greater values than
        #   existing clauses, as an alternative to periodically dividing
        #   the existing heuristic list.
        #   When needed, the whole list is divided by 2^2^8 to keep the whole
        #   thing in reasonable double-precision float territory
        #
        #   The variable chosen for assignment is the unassigned
        #   variable with highest heuristic. False is used, as it is
        #   more common than true for typical planning problems

        for clause in self.CNF_SAT_Problem.Clauses:
            for lit in clause:
                self.persistent_heuristic[lit.ID] += self.curr_heur_val

        self.curr_heur_val = self.curr_heur_val * self.heur_factor

        # Seed the RNG
        random.seed()

        return


    #   Update the heuristic and choose the next assignment to try
    #
    #   Returns the ID for the literal to set
    def Update_Heur(self):
        # We're using a modified VSIDS heuristic:
        #   The number of clauses a variable appears in is counted.
        #   These counts are updated whenever clauses are learned.
        #   Newly-learned clauses are weighted with greater values than
        #   existing clauses, as an alternative to periodically dividing
        #   the existing heuristic list.
        #   When needed, the whole list is divided by 2^2^8 to keep the whole
        #   thing in reasonable double-precision float territory
        #
        #   The variable chosen for assignment is the unassigned
        #   variable with highest heuristic. False is used, as it is
        #   more common than true for typical planning problems
        #
        #   Return value is the index for the next assignment to try

        for clause in self.learned_clause:
            for lit in clause:
                self.persistent_heuristic[lit.ID] += self.curr_heur_val

        if self.learned_clause:
            # Remove the learned clause now that it's been accounted for
            # Don't try this on an empty list...
            self.learned_clause.pop()

        self.curr_heur_val = self.curr_heur_val * self.heur_factor

        # Keep things representable by doubles
        if max(self.persistent_heuristic) > 2**512:
            self.persistent_heuristic[:] = [x / 2**256 for x in self.persistent_heuristic]
            self.curr_heur_val = self.INIT_HEUR

        # Occasionally try a random assignment
        if self.TRY_RANDOM_CHOICE:
            rnd_no = random.randint(1, 100)
            if rnd_no < self.RANDOM_CHOICE_LKHD:
                # Do a random assignment instead
                rnd_no = random.randint(0, len(self.Assignments) - 1)
                # Check that the chosen variable is unassigned
                while self.Assignments[rnd_no] != None:
                    rnd_no = random.randint(0, len(self.Assignments) - 1)
                return rnd_no

        # Choose the greatest unassigned value
        unassigned_lits = [i for i in range(self.nvars) if self.Assignments[i] == None]

        chosen_lit = unassigned_lits[0]
        max_heur = self.persistent_heuristic[chosen_lit]
        for i in unassigned_lits[1:]:
            if self.persistent_heuristic[i] > max_heur:
                if self.Assignments[i] == None:
                    max_heur = self.persistent_heuristic[i]
                    chosen_lit = i

        return chosen_lit

    
    # Backs up until the last guess that still has an untried option
    #
    # Returns false if no guesses were made (problem is UNSAT
    # #)
    def BackTrack(self):
        # Start by learning the conflict clause
        if self.LIMIT_LEARN_CLAUSE_LEN:
            if len(self.Assignments) < self.MAX_LEARN_CLAUSE_LEN:
                new_clause = []
                for i in self.Guesses:
                    lit_val = self.Assignments[i.Lit_ID]
                    lit_i = Literal(i.Lit_ID, lit_val)
                    new_clause.append(lit_i)
        else:
            new_clause = []
            for i in self.Guesses:
                lit_val = self.Assignments[i.Lit_ID]
                lit_i = Literal(i.Lit_ID, lit_val)
                new_clause.append(lit_i)

            # Insert the new clause into the problem and into the learned clauses list
            self.CNF_SAT_Problem.Clauses.append(new_clause)
            self.learned_clause.append(new_clause)

        while(self.Guesses):
            this_Guess = self.Guesses.pop()
            # Determine which guess, if any, is left.
            # If none are left, we pop another
            Untried = [a for a in this_Guess.Tried if this_Guess.Tried[a]==False]
            if(Untried):
                Untried = Untried[0]
                this_Guess.Tried[Untried] = True
                self.Assignments = this_Guess.Assignments_Before
                self.Assignments[this_Guess.Lit_ID] = bool(Untried)
                self.CNF_SAT_Problem = this_Guess.Sentence_Before
                self.Guesses.append(this_Guess)
                self.Unsolvable = False
                if(self.DEBUG):
                    print('Guesses list: %s'%self.Guesses)
                    print('Complexity of recovered state: %d'%complexity(self.CNF_SAT_Problem))
                return True
            #~ else:
                #~ self.Assignments[this_Guess.Lit_ID] = None;
                #~ continue;

        return False

# Useful class to keep general info on the literals
class Literal_Info:
    N_Appear = 0 # Num of clauses it appears in. Negative if impure
    PureAffirm = None # This pure literal has which affirm

    # For debugging:
    def __repr__(self):
        if(self.N_Appear < 0):
            return '<Impure>'
        else:
            return '<%s,%d>'%(self.PureAffirm, self.N_Appear);


# Class that maintains info on guesses made
class Guess:
    def __init__(self):
        self.Lit_ID = -1
        self.Tried = [False]*2
        self.Sentence_Before = SAT_Sentence()
        self.Assignments_Before = []

    # For debugging:
    def __repr__(self):
        return '<%d, %s>'%(self.Lit_ID+1, self.Tried)


def ass_print(assignments):
    ass_L = len(assignments)
    L = ass_L//10
    if( ass_L%10 ):
        L+=1
    for i in range(L):
        print('(%d-%d) - %s'%(i*10+1,min(i*10+10,ass_L),assignments[i*10:min(i*10+10,ass_L)]))
