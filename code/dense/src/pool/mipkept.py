# thin glue: MIP (HiGHS native) on the zero-reduced-cost columns; usage: mipkept.py m kept.npy tight tl presolve(on/off) [heur]
import sys, numpy as np, highspy
m=int(sys.argv[1]); n=2*m; tl=float(sys.argv[4]); pre=sys.argv[5]
d=np.load(sys.argv[2]); masks=np.frombuffer(d[:,:8].tobytes(),dtype='<u8'); cost=d[:,8].astype(np.float64); K=len(masks)
tight=[int(x) for x in open(sys.argv[3]).read().split()]
cnts=[];rws=[]
for a in range(0,K,200000):
    b=((masks[a:a+200000,None]>>np.arange(n,dtype=np.uint64)[None,:])&np.uint64(1)).astype(bool); cnts.append(b.sum(1)); rws.append(np.nonzero(b)[1].astype(np.int32))
st=np.concatenate([[0],np.cumsum(np.concatenate(cnts))]).astype(np.int32); rows=np.concatenate(rws)
inf=highspy.kHighsInf; L=highspy.HighsLp(); L.num_col_=K; L.num_row_=n; L.col_cost_=cost; L.col_lower_=np.zeros(K); L.col_upper_=np.ones(K)
L.row_lower_=np.ones(n); ub=np.full(n,inf); ub[tight]=1.0; L.row_upper_=ub
L.a_matrix_.format_=highspy.MatrixFormat.kColwise; L.a_matrix_.start_=st; L.a_matrix_.index_=rows; L.a_matrix_.value_=np.ones(len(rows))
L.integrality_=[highspy.HighsVarType.kInteger]*K
h=highspy.Highs(); h.setOptionValue("time_limit",tl); h.setOptionValue("presolve",pre); h.setOptionValue("mip_rel_gap",0.0)
if len(sys.argv)>6: h.setOptionValue("mip_heuristic_effort",float(sys.argv[6]))
h.passModel(L); h.run()
print("status",h.modelStatusToString(h.getModelStatus()),"obj",h.getInfo().objective_function_value,flush=True)
if h.getInfo().primal_solution_status==2:
    x=np.array(h.getSolution().col_value); sel=np.nonzero(x>0.5)[0]; out=[(int(masks[j]),int(cost[j])) for j in sel]
    print("SUM",sum(c for _,c in out),"SOL",[(bin(a).count('1'),c) for a,c in out]); open(sys.argv[2]+".sol","w").write("\n".join(f"{a} {c}" for a,c in out))
