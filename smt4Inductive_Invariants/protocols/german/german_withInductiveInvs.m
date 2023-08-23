const


  NODE_NUM : 2;
  DATA_NUM : 2;

type

  NODE : scalarset(NODE_NUM);
  DATA : scalarset(DATA_NUM);

  OTHER : enum {Other};

  CACHE_STATE : enum{I,S,E};
  CACHE : record
    State : CACHE_STATE;
    Data : DATA;
  end;

  MSG_CMD : enum{Empty,ReqS,ReqE,Inv,InvAck,GntS,GntE};

  MSG : record
    Cmd : MSG_CMD;
    Data : DATA;
  end;

var

  Cache : array [NODE] of CACHE;
  Chan1 : array [NODE] of MSG;
  Chan2 : array [NODE] of MSG;
  Chan3 : array [NODE] of MSG;
  InvSet : array [NODE] of boolean;
  ShrSet : array [NODE] of boolean;
  ExGntd : boolean;
  CurCmd : MSG_CMD;
  MemData : DATA;
  AuxData : DATA;

startstate "Init"
for d : DATA do
  for i : NODE do
    Chan1[i].Cmd := Empty;
    Chan2[i].Cmd := Empty;
    Chan3[i].Cmd := Empty;
    Cache[i].State := I;
    InvSet[i] := false;
    ShrSet[i] := false;
  end;
  MemData := d;
  AuxData := d;
end;
  ExGntd := false;
  CurCmd := Empty;
endstartstate;

ruleset  i : NODE do
rule "RecvGntE"
  Chan2[i].Cmd = GntE
==>
begin
  Cache[i].State := E;
  Cache[i].Data := Chan2[i].Data;
  Chan2[i].Cmd := Empty;
  undefine Chan2[i].Data;
endrule;
endruleset;

ruleset  i : NODE do
rule "RecvGntS"
  Chan2[i].Cmd = GntS
==>
begin
  Cache[i].State := S;
  Cache[i].Data := Chan2[i].Data;
  Chan2[i].Cmd := Empty;
  undefine Chan2[i].Data;
endrule;
endruleset;

ruleset  i : NODE do
rule "SendGntE"
  CurCmd = ReqE &
  Chan2[i].Cmd = Empty &
  ExGntd = false &
  forall j : NODE do
    ShrSet[j] = false
  end
==>
begin
  Chan2[i].Cmd := GntE;
  Chan2[i].Data := MemData;
  ShrSet[i] := true;
  ExGntd := true;
  CurCmd := Empty;
endrule;
endruleset;

ruleset  i : NODE do
rule "SendGntS"
  CurCmd = ReqS &
  Chan2[i].Cmd = Empty &
  ExGntd = false
==>
begin
  Chan2[i].Cmd := GntS;
  Chan2[i].Data := MemData;
  ShrSet[i] := true;
  CurCmd := Empty;
endrule;
endruleset;

ruleset  i : NODE do
rule "RecvInvAck1"
  Chan3[i].Cmd = InvAck &
  CurCmd != Empty &
  ExGntd = true
==>
begin
  Chan3[i].Cmd := Empty;
  ShrSet[i] := false;
  ExGntd := false;
  MemData := Chan3[i].Data;
  undefine Chan3[i].Data;
endrule;
endruleset;

ruleset  i : NODE do
rule "RecvInvAck2"
  Chan3[i].Cmd = InvAck &
  CurCmd != Empty &
  ExGntd != true
==>
begin
  Chan3[i].Cmd := Empty;
  ShrSet[i] := false;
endrule;
endruleset;

ruleset  i : NODE do
rule "SendInvAck"
  Chan2[i].Cmd = Inv &
  Chan3[i].Cmd = Empty &
  Cache[i].State = E
==>
begin
  Chan2[i].Cmd := Empty;
  Chan3[i].Cmd := InvAck;
  Chan3[i].Data := Cache[i].Data;
  Cache[i].State := I;
  undefine Cache[i].Data;
endrule;
endruleset;

ruleset  i : NODE do
rule "SendInvAck"
  Chan2[i].Cmd = Inv &
  Chan3[i].Cmd = Empty &
  Cache[i].State != E
==>
begin
  Chan2[i].Cmd := Empty;
  Chan3[i].Cmd := InvAck;
  Cache[i].State := I;
  undefine Cache[i].Data;
endrule;
endruleset;

ruleset  i : NODE do
rule "SendInv1"
  Chan2[i].Cmd = Empty &
  InvSet[i] = true &
  CurCmd = ReqE
==>
begin
  Chan2[i].Cmd := Inv;
  InvSet[i] := false;
endrule;
endruleset;

ruleset  i : NODE do
rule "SendInv2"
  Chan2[i].Cmd = Empty &
  InvSet[i] = true &
  CurCmd = ReqS &
  ExGntd = true
==>
begin
  Chan2[i].Cmd := Inv;
  InvSet[i] := false;
endrule;
endruleset;

ruleset  i : NODE do
rule "RecvReqE"
  CurCmd = Empty &
  Chan1[i].Cmd = ReqE
==>
begin
  CurCmd := ReqE;
  Chan1[i].Cmd := Empty;
  for j : NODE do
    InvSet[j] := ShrSet[j];
  endfor;
endrule;
endruleset;

ruleset  i : NODE do
rule "RecvReqS"
  CurCmd = Empty &
  Chan1[i].Cmd = ReqS
==>
begin
  CurCmd := ReqS;
  Chan1[i].Cmd := Empty;
  for j : NODE do
    InvSet[j] := ShrSet[j];
  endfor;
endrule;
endruleset;

ruleset  i : NODE do
rule "SendReqE1"
  Chan1[i].Cmd = Empty &
  Cache[i].State = I
==>
begin
  Chan1[i].Cmd := ReqE;
endrule;
endruleset;

ruleset  i : NODE do
rule "SendReqE2"
  Chan1[i].Cmd = Empty &
  Cache[i].State = S
==>
begin
  Chan1[i].Cmd := ReqE;
endrule;
endruleset;

ruleset  i : NODE do
rule "SendReqS"
  Chan1[i].Cmd = Empty &
  Cache[i].State = I
==>
begin
  Chan1[i].Cmd := ReqS;
endrule;
endruleset;

ruleset  d : DATA; i : NODE do
rule "Store"
  Cache[i].State = E
==>
begin
  Cache[i].Data := d;
  AuxData := d;
endrule;
endruleset;

invariant "CntrlProp"
  forall i : NODE do
    forall j : NODE do
      (i != j ->
      ((Cache[i].State = E ->
      Cache[j].State = I) &
      (Cache[i].State = S ->
      (Cache[j].State = I |
      Cache[j].State = S))))
    end
  end;


invariant "DataProp"
  ((ExGntd = false ->
  MemData = AuxData) &
  forall i : NODE do
    forall j : NODE do
    (i !=j ->
    (Cache[i].State != I ->
    Cache[i].Data = AuxData) &
    (Cache[j].State != I ->
    Cache[j].Data = AuxData))
    end
  end);

invariant "CntrlProp_RecvGntE1"
  forall i : NODE do
    forall j : NODE do
      !(Cache[j].State = E & Chan2[i].Cmd = GntE)
end  end  ;;

invariant "CntrlProp_RecvGntE2"
  forall j : NODE do
    forall i : NODE do
      !(Cache[i].State = S & Chanj[j].Cmd = GntE)
end  end  ;;

invariant "CntrlProp_RecvGntS1"
  forall i : NODE do
    forall j : NODE do
      !(Cache[j].State = E & Chan2[i].Cmd = GntS)
end  end  ;;

invariant "DataProp_RecvGntE1"
  forall i : NODE do
    !(ExGntd = false & Chan2[i].Cmd = GntE)
end  ;;

invariant "DataProp_RecvGntS1"
  forall i : NODE do
    forall i : NODE do
      !(Chan2[i].Data != MemData & Chan2[i].Cmd = GntS)
end  end  ;;

invariant "DataProp_RecvInvAck11"
  forall i : NODE do
    forall i : NODE do
      !(Chan3[i].Data != AuxData & Chan3[i].Cmd = InvAck & CurCmd = ReqS)
end  end  ;;

invariant "DataProp_RecvInvAck11"
  forall i : NODE do
    forall i : NODE do
      !(Chan3[i].Data != AuxData & Chan3[i].Cmd = InvAck & ExGntd = true)
end  end  ;;

invariant "DataProp_RecvInvAck11"
!(CurCmd = Inv)
;;

invariant "DataProp_Store1"
  forall i : NODE do
    !(ExGntd = false & Cache[i].State = E)
end  ;;

invariant "DataProp_Store2"
  forall j : NODE do
    forall i : NODE do
      !(Cache[i].State = S & Cache[j].State = E)
end  end  ;;

invariant "DataProp_Store2"
  forall j : NODE do
    forall i : NODE do
      !(Cache[i].State = E & Cache[j].State = E)
end  end  ;;

invariant "CntrlProp_RecvGntE1_1_RecvGntE2"
  forall j : NODE do
    forall i : NODE do
      !(Chan2[i].Cmd = GntE & Chanj[j].Cmd = GntE)
end  end  ;;

invariant "CntrlProp_RecvGntE2_1_RecvGntS1"
  forall i : NODE do
    forall j : NODE do
      !(Chanj[j].Cmd = GntE & Chan2[i].Cmd = GntS)
end  end  ;;

invariant "CntrlProp_RecvGntE2_1_SendGntE2"
  forall i : NODE do
    forall i : NODE do
      !(Cache[i].State = S & ShrSet[i] = false)
end  end  ;;

invariant "DataProp_RecvGntE1_1_RecvInvAck11"
  forall i : NODE do
    forall i : NODE do
      !(Chan2[i].Cmd = GntE & Chan3[i].Cmd = InvAck)
end  end  ;;

invariant "DataProp_RecvGntE1_1_RecvInvAck12"
  forall j : NODE do
    forall i : NODE do
      !(Chan2[i].Cmd = GntE & Chan3[j].Cmd = InvAck)
end  end  ;;

invariant "DataProp_RecvGntS1_1_RecvInvAck11"
  forall i : NODE do
    forall i : NODE do
      !(Chan2[i].Cmd = GntS & Chan3[i].Cmd = InvAck)
end  end  ;;

invariant "DataProp_RecvGntS1_1_RecvInvAck12"
  forall i : NODE do
    !(Chan2[i].Cmd = GntS & ExGntd = true)
end  ;;

invariant "DataProp_RecvGntS1_1_RecvInvAck12"
  forall j : NODE do
    forall i : NODE do
      !(Chan2[i].Cmd = GntS & CurCmd = ReqS & Chan3[j].Cmd = InvAck)
end  end  ;;

invariant "DataProp_RecvInvAck11_1_SendInvAck1"
  forall i : NODE do
    forall i : NODE do
      !(Cache[i].State = I & Chan2[i].Cmd = Inv)
end  end  ;;

invariant "DataProp_RecvInvAck11_1_Store1"
  forall i : NODE do
    forall i : NODE do
      !(Chan3[i].Cmd = InvAck & Cache[i].State = E)
end  end  ;;

invariant "DataProp_RecvInvAck11_1_Store2"
  forall j : NODE do
    forall i : NODE do
      !(Chan3[i].Cmd = InvAck & Cache[j].State = E)
end  end  ;;

invariant "DataProp_RecvInvAck11_2_SendGntE1"
  forall i : NODE do
    forall i : NODE do
      !(Chan3[i].Cmd = InvAck & ShrSet[i] = false)
end  end  ;;

invariant "DataProp_RecvInvAck11_2_SendInvAck1"
  forall i : NODE do
    !(ExGntd = true & Cache[i].State = S)
end  ;;

invariant "CntrlProp_RecvGntE2_1_RecvGntS1_1_SendGntE2"
  forall i : NODE do
    forall i : NODE do
      !(Chan2[i].Cmd = GntS & ShrSet[i] = false)
end  end  ;;

invariant "CntrlProp_RecvGntE2_1_SendGntE2_1_RecvInvAck11"
  forall i : NODE do
    forall i : NODE do
      !(Cache[i].State = S & Chan3[i].Cmd = InvAck)
end  end  ;;

invariant "DataProp_RecvGntE1_1_RecvInvAck12_1_SendInvAck2"
  forall j : NODE do
    forall i : NODE do
      !(Chan2[i].Cmd = GntE & Chanj[j].Cmd = Inv)
end  end  ;;

invariant "DataProp_RecvGntS1_1_RecvInvAck11_1_SendGntS1"
  forall i : NODE do
    !(Chan3[i].Cmd = InvAck & ExGntd = false & CurCmd = ReqS)
end  ;;

invariant "DataProp_RecvGntS1_1_RecvInvAck12_2_SendInvAck2"
  forall j : NODE do
    forall j : NODE do
      !(CurCmd = ReqS & Cache[j].State = S & Chanj[j].Cmd = Inv)
end  end  ;;

invariant "DataProp_RecvInvAck11_1_SendInvAck1_1_SendInv11"
  forall i : NODE do
    forall i : NODE do
    forall i : NODE do
        !(Cache[i].State = I & InvSet[i] = true & Chan2[i].Cmd = Empty)
end  end  end  ;;
