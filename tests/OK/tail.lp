constant symbol N:TYPE
constant symbol o : N
constant symbol s : N→N

constant symbol A:TYPE

constant symbol V:N→TYPE
constant symbol nil:V o
constant symbol cons:A→Πn,V n→V(s n)

symbol tail:Πn,V(s n)→V n

//set debug +sui
rule tail _ (cons _ _ $v) ↪ $v
