# thin glue (stateless, one shot, < 5 min, small model): master LP / MIP via HiGHS.
# usage: lp.py lp|mip m cols.bin out.txt [tl] [threads]
# cols.bin: K records of 16 bytes (u128 LE mask, bit x-1 <-> velocity x). Rows x=1..2m: Low (x<=m+1) cover >=1 with
# slack column cost 1; Y rows (x>=m+2) packing <=1. Objective: sum of slacks.
import sys, numpy as np, highspy
mode=sys.argv[1]; m=int(sys.argv[2]); fn=sys.argv[3]; out=sys.argv[4]; tl=float(sys.argv[5]) if len(sys.argv)>5 else 60.0
thr=int(sys.argv[6]) if len(sys.argv)>6 else 4
n=2*m; nl=m+1
raw=np.fromfile(fn,dtype='<u8').reshape(-1,2); K=len(raw)
assert K<=600000
cnts=[];rws=[]
for a in range(0,K,100000):
    lo=raw[a:a+100000,0]; hi=raw[a:a+100000,1]
    B=np.zeros((len(lo),n),dtype=bool)
    for b in range(n):
        B[:,b]=((lo>>np.uint64(b))&np.uint64(1)).astype(bool) if b<64 else ((hi>>np.uint64(b-64))&np.uint64(1)).astype(bool)
    cnts.append(B.sum(1)); rws.append(np.nonzero(B)[1].astype(np.int32))
cnt=np.concatenate(cnts) if cnts else np.zeros(0,dtype=np.int64); rows=np.concatenate(rws) if rws else np.zeros(0,dtype=np.int32)
# append slack columns: one per Low row
st=np.concatenate([[0],np.cumsum(cnt)]).astype(np.int32)
st=np.concatenate([st,st[-1]+np.arange(1,nl+1,dtype=np.int32)]); rows=np.concatenate([rows,np.arange(nl,dtype=np.int32)])
C=K+nl; integer=(mode=="mip"); inf=highspy.kHighsInf
L=highspy.HighsLp(); L.num_col_=C; L.num_row_=n
cost=np.zeros(C); cost[K:]=1.0; L.col_cost_=cost; L.col_lower_=np.zeros(C); L.col_upper_=np.full(C,1.0 if integer else inf)
if not integer: L.col_upper_=np.concatenate([np.full(K,inf),np.ones(nl)])
rl=np.concatenate([np.ones(nl),np.full(n-nl,-inf)]); ru=np.concatenate([np.full(nl,inf),np.ones(n-nl)])
L.row_lower_=rl; L.row_upper_=ru
L.a_matrix_.format_=highspy.MatrixFormat.kColwise; L.a_matrix_.start_=st; L.a_matrix_.index_=rows; L.a_matrix_.value_=np.ones(len(rows))
if integer: L.integrality_=[highspy.HighsVarType.kInteger]*C
h=highspy.Highs(); h.setOptionValue("output_flag",False); h.setOptionValue("threads",thr)
if integer:
    h.setOptionValue("time_limit",tl); h.setOptionValue("mip_rel_gap",0.0)
h.passModel(L); h.run()
info=h.getInfo(); sol=h.getSolution()
with open(out+".tmp","w") as f:
    f.write("status %s\n"%h.modelStatusToString(h.getModelStatus()).replace(" ","_"))
    f.write("obj %.9f\n"%info.objective_function_value)
    if integer:
        if info.primal_solution_status==2:
            x=np.array(sol.col_value); f.write("sel "+" ".join(str(int(i)) for i in np.nonzero(x[:K]>0.5)[0])+"\n")
            f.write("unc "+" ".join(str(i+1) for i in np.nonzero(x[K:]>0.5)[0])+"\n")
        else: f.write("nosol\n")
        f.write("bound %.9f\n"%info.mip_dual_bound)
    else:
        f.write("dual "+" ".join("%.9g"%d for d in sol.row_dual)+"\n")
        x=np.array(sol.col_value); f.write("nnz %d\n"%int((x[:K]>1e-9).sum()))
import os; os.replace(out+".tmp",out)
