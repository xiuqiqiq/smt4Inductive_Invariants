const
    NODENUMS : 2;

type
    state : enum{I, T, C, E};
    NODE: 1..NODENUMS;

var
    n : array [NODE] of state;
    x : boolean;

startstate "Init"
for i: NODE do
    n[i] :=I;
endfor;
x := true;
endstartstate;

ruleset i : NODE
do rule "Try"
  n[i] = I
==>
begin
  n[i] :=T;
endrule;endruleset;

ruleset i : NODE
do rule "Crit"
  n[i] = T & x = true
==>
begin
  n[i] := C;
  x := false;
endrule;endruleset;

ruleset i : NODE
do rule "Exit"
  n[i] =C
==>
begin
  n[i] := E;
endrule;endruleset;

ruleset i : NODE
do rule "Idle"
  n[i] = E
==>
begin
  n[i] := I;
  x := true;
endrule;endruleset;

invariant "mutualEx"
forall i : NODE do forall j : NODE do
i != j ->
    (n[i] = C -> n[j] != C)
end  end;
invariant "mutualEx_Crit1"
  forall j : NODE do
    !(n[j] = C & x = true)
end  ;

invariant "mutualEx_Crit1_1_Idle1"
  forall i : NODE do
    forall j : NODE do
      !(n[j] = C & n[i] = E)
end  end  ;

invariant "mutualEx_Crit1_1_Idle1_1_Crit2"
  forall i : NODE do
    !(n[i] = E & x = true)
end  ;

invariant "mutualEx_Crit1_1_Idle1_1_Crit2_1_Idle2"
  forall j : NODE do
    forall i : NODE do
      !(n[i] = E & n[j] = E)
end  end  ;
