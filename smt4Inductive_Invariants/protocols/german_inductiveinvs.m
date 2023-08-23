invariant "inv_51"
  forall i : NODE do
    forall j : NODE do
    (i!=j ->
    (((ShrSet[i] = true) & (ExGntd = true)) & (ShrSet[j] = true)))
    end
  end;

invariant "inv_50"
  forall i : NODE do
    forall j : NODE do
    (i!=j ->
    (((InvSet[i] = true) & (ExGntd = true)) & (InvSet[j] = true)))
    end
  end;

invariant "inv_49"
  forall i : NODE do
    forall j : NODE do
    (i!=j ->
    (((CurCmd = ReqS) & (InvSet[i] = true)) & (Chan2[j].Cmd = Inv)))
    end
  end;

invariant "inv_48"
  forall i : NODE do
    forall j : NODE do
    (i!=j ->
    (((Chan2[i].Cmd = Inv) & (CurCmd = ReqS)) & (Chan2[j].Cmd = Inv)))
    end
  end;

invariant "inv_47"
  forall i : NODE do
    forall j : NODE do
    (i!=j ->
    (((CurCmd = ReqS) & (Chan3[i].Cmd = InvAck)) & (InvSet[j] = true)))
    end
  end;
 
invariant "inv_46"
  forall i : NODE do
    forall j : NODE do
    (i!=j ->
    (((Chan3[i].Cmd = InvAck) & (CurCmd = ReqS)) & (Chan3[j].Cmd = InvAck)))
    end
  end;

invariant "inv_45"
  forall i : NODE do
    forall j : NODE do
    (i!=j ->
    (((Chan2[i].Cmd = Inv) & (CurCmd = ReqS)) & (Chan3[j].Cmd = InvAck)))
    end
  end;

invariant "inv_44"
  forall i : NODE do
    (((Chan3[i].Cmd = InvAck) & (CurCmd = ReqS)) & (ExGntd = false))
  end;

invariant "inv_43"
  forall i : NODE do
    ((Chan3[i].Cmd = InvAck) & (CurCmd = Empty))
  end;


invariant "inv_42"
  forall i : NODE do
    (((Chan2[i].Cmd = Inv) & (CurCmd = ReqS)) & (ExGntd = false))
  end;

invariant "inv_41"
  forall i : NODE do
    forall j : NODE do
    (i!=j ->
    ((Chan2[i].Cmd = GntE) & (ShrSet[j] = true)))
    end
  end;
 
invariant "inv_40"
  forall i : NODE do
    ((Chan2[i].Cmd = GntS) & (Chan3[i].Cmd = InvAck))
  end;

invariant "inv_39"
  forall i : NODE do
    ((InvSet[i] = true) & (Chan3[i].Cmd = InvAck))
  end;

invariant "inv_38"
  forall i : NODE do
    ((CurCmd = Empty) & (Chan2[i].Cmd = Inv))
  end;

invariant "inv_37"
  forall i : NODE do
    forall j : NODE do
    (i!=j ->
    ((Cache[i].State = E) & (ShrSet[j] = true)))
    end
  end;

invariant "inv_36"
  forall i : NODE do
    forall j : NODE do
    (i!=j ->
    ((Chan2[i].Cmd = GntE) & (InvSet[j] = true)))
    end
  end;
  
invariant "inv_35"
  forall i : NODE do
    ((ShrSet[i] = false) & (Chan2[i].Cmd = GntE))
  end;

invariant "inv_34"
  forall i : NODE do
    ((!(Cache[i].State = I)) & (Chan3[i].Cmd = InvAck))
  end;

invariant "inv_33"
  forall i : NODE do
    ((Chan2[i].Cmd = GntS) & (ShrSet[i] = false))
  end;

invariant "inv_32"
  forall i : NODE do
    ((Chan2[i].Cmd = Inv) & (Chan3[i].Cmd = InvAck))
  end;

invariant "inv_31"
  forall i : NODE do
    ((ExGntd = true) & (Chan2[i].Cmd = GntS))
  end;

invariant "inv_30"
  forall i : NODE do
    ((InvSet[i] = true) & (ShrSet[i] = false))
  end;

invariant "inv_29"
  forall i : NODE do
    ((InvSet[i] = true) & (Chan2[i].Cmd = Inv))
  end;

invariant "inv_28"
  forall i : NODE do
    (((((ExGntd = true) & (!(Cache[i].State = E))) & (Chan2[i].Cmd = Empty)) & (ShrSet[i] = true)) & (CurCmd = Empty))
  end;

invariant "inv_27"
  forall i : NODE do
    forall j : NODE do
    (i!=j ->
    ((Cache[j].State = E) & (InvSet[i] = true)))
    end
  end;

invariant "inv_26"
  forall i : NODE do
    forall j : NODE do
    (i!=j ->
    ((Chan2[i].Cmd = GntE) & (Chan2[j].Cmd = Inv)))
    end
  end;

invariant "inv_25"
  forall i : NODE do
    forall j : NODE do
    (i!=j ->
    ((Chan2[i].Cmd = GntE) & (Chan2[j].Cmd = GntE)))
    end
  end;

invariant "inv_24"
  forall i : NODE do
    ((!(Cache[i].State = I)) & (ShrSet[i] = false))
    end
  end;

invariant "inv_23"
  forall i : NODE do
    forall j : NODE do
    (i!=j ->
    ((Chan2[j].Cmd = GntS) & (Chan2[i].Cmd = GntE)))
    end
  end;

invariant "inv_22"
  forall i : NODE do
    ((Chan2[i].Cmd = Inv) & (ShrSet[i] = false))
  end;

invariant "inv_21"
  forall i : NODE do
    ((((ExGntd = true) & (!(Cache[i].State = E))) & (Chan2[i].Cmd = Empty)) & (InvSet[i] = true))
  end;

invariant "inv_20"
  forall i : NODE do
    forall j : NODE do
    (i!=j ->
    ((Cache[j].State = E) & (Chan2[i].Cmd = Inv)))
    end
  end;

invariant "inv_19"
  forall i : NODE do
    forall j : NODE do
    (i!=j ->
    ((Chan2[j].Cmd = GntE) & (Chan3[i].Cmd = InvAck)))
    end
  end;

invariant "inv_18"
  forall i : NODE do
    ((Chan2[i].Cmd = GntE) & (Chan3[i].Cmd = InvAck))
  end;

invariant "inv_17"
  forall i : NODE do
    ((Chan2[i].Cmd = GntE) & (Cache[i].State = E))
  end;

invariant "inv_16"
  forall i : NODE do
    ((Chan2[i].Cmd = GntS) & (Cache[i].State = E))
  end;

invariant "inv_15"
  forall i : NODE do
    forall j : NODE do
    (i!=j ->
    ((Cache[j].State = E) & (Chan2[i].Cmd = GntE)))
    end
  end;

invariant "inv_14"
  forall i : NODE do
    forall j : NODE do
    (i!=j ->
    ((!(Cache[i].State = I)) & (Chan2[j].Cmd = GntE)))
    end
  end;

invariant "inv_13"
  forall i : NODE do
    forall j : NODE do
    (i!=j ->
    ((Cache[j].State = E) & (Chan2[i].Cmd = GntS)))
    end
  end;

invariant "inv_12"
  forall i : NODE do
    ((Chan3[i].Cmd = InvAck) & (ShrSet[i] = false))
  end;

invariant "inv_11"
  forall i : NODE do
    (((ExGntd = true) & (!(Cache[i].State = E))) & (Chan2[i].Cmd = Inv))
  end;

invariant "inv_10"
  forall i : NODE do
    ((ExGntd = false) & (Chan2[i].Cmd = GntE))
  end;

invariant "inv_9"
  forall i : NODE do
    forall j : NODE do
    (i!=j ->
    ((Cache[j].State = E) & (Chan3[i].Cmd = InvAck)))
    end
  end;

invariant "inv_8"
  forall i : NODE do
    ((Cache[i].State = E) & (Chan3[i].Cmd = InvAck))
  end;

invariant "inv_7"
  forall i : NODE do
    ((!(Chan2[i].Data = AuxData)) & (Chan2[i].Cmd = GntE))
  end;

invariant "inv_6"
  forall i : NODE do
    ((!(Chan2[i].Data = AuxData)) & (Chan2[i].Cmd = GntS))
  end;

invariant "inv_5"
  forall i : NODE do
    forall j : NODE do
    (i!=j ->
    ((!(Cache[j].State = I)) & (Cache[i].State = E)))
    end
  end;

invariant "inv_4"
  forall i : NODE do
    (((!(Chan3[i].Data = AuxData)) & (ExGntd = true)) & (Chan3[i].Cmd = InvAck))
  end;

invariant "inv_3"
  forall i : NODE do
    ((ExGntd = false) & (Cache[i].State = E))
  end;

invariant "inv_3"
  forall i : NODE do
    ((ExGntd = false) & (Cache[i].State = E))
  end;

invariant "inv_2"
  forall i : NODE do
    ((!(Cache[i].State = I)) & (!(Cache[i].Data = AuxData)))
  end;

invariant "inv_1"
  ((ExGntd = false) & (!(MemData = AuxData)))