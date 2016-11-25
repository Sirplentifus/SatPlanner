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

