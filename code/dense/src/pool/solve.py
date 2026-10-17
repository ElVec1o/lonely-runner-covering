# thin glue: read pool.bin (numpy.fromfile), build set-cover MIP, call HiGHS (native), print/save chosen parts.
# usage: python3 -u solve.py m pool.bin timelimit [lp]
import sys, numpy as np, highspy, time
m=int(sys.argv[1]); fn=sys.argv[2]; tl=float(sys.argv[3]); lp=len(sys.argv)>4
dt=np.dtype([('mask','<u8'),('c','u1')]); raw=np.fromfile(fn,dtype=np.dtype('u1')).reshape(-1,9)
masks=np.frombuffer(raw[:,:8].tobytes(),dtype='<u8'); cost=raw[:,8].astype(np.float64)
P=len(masks); n=2*m; print("parts",P,flush=True)
# dominance: drop nothing here
h=highspy.Highs(); h.setOptionValue("output_flag",True); h.setOptionValue("time_limit",tl); h.setOptionValue("threads",4)
inf=highspy.kHighsInf
# CSC: column j has rows = set bits
starts=[0]; idx=[]
cnts=[];rws=[]
for a in range(0,P,200000):
    mk=masks[a:a+200000]
    b=((mk[:,None]>>np.arange(n,dtype=np.uint64)[None,:])&np.uint64(1)).astype(bool)
    cnts.append(b.sum(1)); rws.append(np.nonzero(b)[1].astype(np.int32))
cnt=np.concatenate(cnts); starts=np.concatenate([[0],np.cumsum(cnt)]).astype(np.int32); rows=np.concatenate(rws)
lp_=highspy.HighsLp(); lp_.num_col_=P; lp_.num_row_=n
lp_.col_cost_=cost; lp_.col_lower_=np.zeros(P); lp_.col_upper_=np.full(P,1.0 if not lp else inf)
lp_.row_lower_=np.ones(n); lp_.row_upper_=np.full(n,inf)
lp_.a_matrix_.format_=highspy.MatrixFormat.kColwise
lp_.a_matrix_.start_=starts; lp_.a_matrix_.index_=rows; lp_.a_matrix_.value_=np.ones(len(rows))
if not lp: lp_.integrality_=[highspy.HighsVarType.kInteger]*P
h.passModel(lp_); h.run()
info=h.getInfo(); print("status",h.modelStatusToString(h.getModelStatus()),"obj",info.objective_function_value,"bound",getattr(info,'mip_dual_bound',None),flush=True)
if not lp:
    x=np.array(h.getSolution().col_value); sel=np.nonzero(x>0.5)[0]
    out=[]
    for j in sel: out.append((int(masks[j]),int(cost[j])))
    print("SOL",[ (bin(a).count('1'),c) for a,c in out]); print("SUM",sum(c for _,c in out))
    open(fn+".sol","w").write("\n".join(f"{a} {c}" for a,c in out))
