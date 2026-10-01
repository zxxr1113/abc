#include "sat/bsat/satSolver.h"
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <time.h>
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC,&t);return t.tv_sec+1e-9*t.tv_nsec; }
int main(int argc,char **argv) {
 FILE *f,*q,*o; int nv,nc,nq,i,j,n,id,res,conf; lit lits[16]; sat_solver *s; double start;
 assert(argc==4);f=fopen(argv[1],"r");q=fopen(argv[2],"r");o=fopen(argv[3],"w");assert(f&&q&&o);
 assert(fscanf(f,"%d%d",&nv,&nc)==2 && nv>0 && nc>0);s=sat_solver_new();sat_solver_setnvars(s,nv);
 for(i=0;i<nc;i++){assert(fscanf(f,"%d",&n)==1 && n>0 && n<=16);for(j=0;j<n;j++)assert(fscanf(f,"%d",lits+j)==1 && lits[j]>=0 && lits[j]<2*nv);assert(sat_solver_addclause(s,lits,lits+n));}
 fclose(f);assert(fscanf(q,"%d",&nq)==1 && nq>=0);fprintf(o,"query,result,conflicts,wall_s\n");fflush(o);
 for(i=0;i<nq;i++){assert(fscanf(q,"%d%d",&id,&n)==2 && id==i && n>0 && n<=16);for(j=0;j<n;j++)assert(fscanf(q,"%d",lits+j)==1 && lits[j]>=0 && lits[j]<2*nv);conf=sat_solver_nconflicts(s);start=now();res=sat_solver_solve(s,lits,lits+n,1000,0,0,0);fprintf(o,"%d,%d,%d,%.9f\n",id,res,sat_solver_nconflicts(s)-conf,now()-start);fflush(o);}
 fclose(q);fclose(o);sat_solver_delete(s);return 0;
}
