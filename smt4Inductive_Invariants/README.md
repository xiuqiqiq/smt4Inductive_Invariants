
1. 环境准备：
  a. z3-solver
  b. subprocess
  c. LocalSearch(首次运行需重新编译，依赖z3)

2. 协议准备：
  a. 带不变式的完整协议的.m文件
  b. 无不变式的协议.m文件
  c. 上述文件位于同一文件夹内
  
  ---------------------------------------------------------

  TIPS-不变式示例：
  ·不变式coherence实例化为n[1]与n[2]
  invariant "coherence"
    forall i : NODE do
      forall j : NODE do
        i != j -> (n[i].st = C -> n[j].st != C)
  end   end;

  ·为了将不变式实例化为n[1]与n[2]，稍作修改。这样做是为了实例化的时候更方便，不然不变式参数多的时候，类似于coherence，会有n[1].st = C -> n[2].st != C和n[2].st = C -> n[1].st != C两条等价式重复构建F。对称性也允许这么做。
  invariant "c51"
  forall i : NODE do
    forall j : NODE do
    (i != j -> 
    (n[i].st= C -> n[i].data =auxDATA) &
    (n[j].st= C -> n[j].data =auxDATA))
  end   end;

  ---------------------------------------------------------

  TIPS-协议结点数
  · 修改对应的两个.m文件中的NODE数量
  · 若2个NODE，则传参为1 2；3个NODE，则传参为1 2 3 ，以此类推
  ---------------------------------------------------------



3. 运行
  python (PATH).../newSMT.py (PROTOCOLPath+PROTOCOLName) 1 2 ...
  // 示例：python3.8 SMT/newSMT.py protocols/german/german 1 2 3

  生成文件中的PROTOCOLName_invs.txt即为算法找到的辅助不变式