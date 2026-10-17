# thin glue: LP -> duals -> keep zero-reduced-cost columns (valid when target obj == LP opt) -> MIP on reduced pool.
# usage: python3 -u rcfix.py m pool.bin target tl
import sys, numpy as np, highspy
m=int(sys.argv[1]); fn=sys.argv[2]; target=float(sys.argv[3]); tl=float(sys.argv[4]); n=2*m
raw=np.fromfile(fn,dtype=np.uint8).reshape(-1,9)
masks=np.frombuffer(raw[:,:8].tobytes(),dtype='<u8'); cost=raw[:,8].astype(np.float64); P=len(masks)
def build(mk,cs,integer,rowub=None):
    cnts=[];rws=[]
    for a in range(0,len(mk),200000):
        b=((mk[a:a+200000,None]>>np.arange(n,dtype=np.uint64)[None,:])&np.uint64(1)).astype(bool)
        cnts.append(b.sum(1)); rws.append(np.nonzero(b)[1].astype(np.int32))
    cnt=np.concatenate(cnts); st=np.concatenate([[0],np.cumsum(cnt)]).astype(np.int32); rows=np.concatenate(rws)
    L=highspy.HighsLp(); inf=highspy.kHighsInf; k=len(mk); L.num_col_=k; L.num_row_=n
    L.col_cost_=cs; L.col_lower_=np.zeros(k); L.col_upper_=np.full(k,1.0 if integer else inf)
    L.row_lower_=np.ones(n); L.row_upper_=np.full(n,inf) if rowub is None else rowub
    L.a_matrix_.format_=highspy.MatrixFormat.kColwise; L.a_matrix_.start_=st; L.a_matrix_.index_=rows; L.a_matrix_.value_=np.ones(len(rows))
    if integer: L.integrality_=[highspy.HighsVarType.kInteger]*k
    return L,st,rows
h=highspy.Highs(); h.setOptionValue("output_flag",False)
L,st,rows=build(masks,cost,False); h.passModel(L); h.run()
obj=h.getInfo().objective_function_value; y=np.array(h.getSolution().row_dual); print("LP",obj,"P",P,flush=True)
# reduced cost = c - sum y over rows
ya=np.add.reduceat(y[rows],st[:-1]) if len(rows) else 0
cnt=np.diff(st); ya=np.where(cnt>0,ya,0.0); rc=cost-ya
keep=np.nonzero(rc<1e-7)[0]; print("kept",len(keep),"of",P,"min rc",rc.min(),flush=True)
if obj>target+1e-6: print("TARGET BELOW LP: infeasible for this pool (LP bound",obj,")"); sys.exit(0)
rowub=np.where(y>1e-9,1.0,highspy.kHighsInf)
mk=masks[keep]; cs=cost[keep]
h2=highspy.Highs(); h2.setOptionValue("output_flag",True); h2.setOptionValue("time_limit",tl); pass
L2,_,_=build(mk,cs,True,rowub); print('pass',h2.passModel(L2)); print('run',h2.run())
print("status",h2.modelStatusToString(h2.getModelStatus()),"obj",h2.getInfo().objective_function_value,flush=True)
x=np.array(h2.getSolution().col_value)
if len(x) and h2.getInfo().primal_solution_status==2:
    sel=np.nonzero(x>0.5)[0]; out=[(int(mk[j]),int(cs[j])) for j in sel]
    print("SUM",sum(c for _,c in out),"SOL",[(bin(a).count('1'),c) for a,c in out])
    open(fn+".sol","w").write("\n".join(f"{a} {c}" for a,c in out))
