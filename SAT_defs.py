class Literal:
    def __init__(self, ID=-1, Affirm=None):
        self.ID = ID;
        self.Affirm = Affirm; #True if variable is affirmed, False if negated
        
    def __repr__(self):
        
        if(self.Affirm==None or self.ID==-1):
            raise(ValueError('Undefined literal can\'t be printed'));
        
        if(not self.Affirm):
            S = '-';
        else:
            S = '';
        S+='x%d'%self.ID;
        return S;
    
class SAT_Sentence:
    N_Vars = -1;
    Clauses = []; #List of Lists of Literal objects
    
    def __init__(self):
        self.Clauses = [];
        
    def __repr__(self):
        S = '';
        MAX_REPRESENTED = 100;
        if(len(self.Clauses)<=MAX_REPRESENTED):
            S+= '%s'%self.Clauses;
        else:
            S+= '%s (...)'%self.Clauses[:MAX_REPRESENTED];
        S+='-> %d Clauses'%(len(self.Clauses));
        
        if(self.N_Vars>0):
           S+= ' and %d distinct literals'%(self.N_Vars);
        
        return S;
        
def complexity(SAT_phrase):
    ret = 0;
    for Clause in SAT_phrase.Clauses:
        ret += len(Clause);
    return ret;
