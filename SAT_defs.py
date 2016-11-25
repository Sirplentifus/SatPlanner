class Literal:
    VarID = -1;
    Affirm = None; #True if variable is affirmed, False if negated
    
class SAT_Sentence:
    N_Vars = -1;
    Clauses = []; #List of Lists of Literal objects

