grammar btree;


tree
  : NODE LPAREN tree tree RPAREN
  | LEAF flag 


FLAG
   : '1'
   | '0'
   ;

LEAF
   : 'leaf'
   ;
LPAREN
   : 'node'
   ;

LPAREN
   : '('
   ;


RPAREN
   : ')'
   ;

WS
   : [ \r\n\t] + -> skip
   ;
