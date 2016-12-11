import copy;
import pdb;

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
        S+='%d'%(self.ID+1);
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
    
    def __copy__(self):
        ret = SAT_Sentence();
        ret.N_Vars = self.N_Vars;
        ret.Clauses = [];
        for Clause in self.Clauses:
            ret.Clauses.append(copy.copy(Clause));
        return ret;
        
def complexity(SAT_phrase):
    ret = 0;
    for Clause in SAT_phrase.Clauses:
        ret += len(Clause);
    return ret;

def SAT_load(SAT_phrase):
    pass;
    
    
def SAT_save(SAT_phrase, file_name):
    fh = open(file_name, 'w');
    
    fh.write('p cnf %d %d\n'%(SAT_phrase.N_Vars, len(SAT_phrase.Clauses)));
    
    for Clause in SAT_phrase.Clauses:
        for Lit in Clause:
            fh.write('%s '%Lit);
        fh.write('0 \n');
    
    
