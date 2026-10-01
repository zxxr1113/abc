/* Opt-in research solver: same CNF/order/budget as query_solver.c.
 * argc=4 retains the status-only protocol. argc=6 requests step-only projections.
 * Capture follows each SAT solve immediately, before any subsequent solve.
 * Neither this file nor its builder modifies the existing solver or ABC binary.
 */
#include "sat/bsat/satSolver.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#define CHECK(c) do { if (!(c)) { fprintf(stderr,"invalid input at line %d\n",__LINE__); return 2; } } while (0)
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC,&t); return t.tv_sec+1e-9*t.tv_nsec; }
int main(int argc, char **argv) {
 FILE *f,*q,*o,*v=NULL,*m=NULL; int nv,nc,nq,np=0,i,j,n,id,res,conf; int *vars=NULL;
 lit lits[16]; sat_solver *s; double start;
 CHECK(argc==4 || argc==6);
 f=fopen(argv[1],"r"); q=fopen(argv[2],"r"); o=fopen(argv[3],"w"); CHECK(f&&q&&o);
 CHECK(fscanf(f,"%d%d",&nv,&nc)==2 && nv>0 && nc>0); s=sat_solver_new(); sat_solver_setnvars(s,nv);
 for(i=0;i<nc;i++) {
  CHECK(fscanf(f,"%d",&n)==1 && n>0 && n<=16);
  for(j=0;j<n;j++) CHECK(fscanf(f,"%d",lits+j)==1 && lits[j]>=0 && lits[j]<2*nv);
  CHECK(sat_solver_addclause(s,lits,lits+n));
 }
 fclose(f);
 if(argc==6) {
  char phase[16],extra;
  v=fopen(argv[4],"r"); m=fopen(argv[5],"w"); CHECK(v&&m);
  CHECK(fscanf(v,"%15s%d",phase,&np)==2 && !strcmp(phase,"step") && np>=0 && np<nv);
  vars=(int *)malloc(sizeof(int)*(np+1)); CHECK(vars);
  for(i=0;i<np;i++) {
   CHECK(fscanf(v,"%d",vars+i)==1 && vars[i]>0 && vars[i]<nv);
   for(j=0;j<i;j++) CHECK(vars[j]!=vars[i]);
  }
  CHECK(fscanf(v," %c",&extra)==EOF); fclose(v);
 }
 CHECK(fscanf(q,"%d",&nq)==1 && nq>=0); fprintf(o,"query,result,conflicts,wall_s\n"); fflush(o);
 for(i=0;i<nq;i++) {
  CHECK(fscanf(q,"%d%d",&id,&n)==2 && id==i && n>0 && n<=16);
  for(j=0;j<n;j++) CHECK(fscanf(q,"%d",lits+j)==1 && lits[j]>=0 && lits[j]<2*nv);
  conf=sat_solver_nconflicts(s); start=now(); res=sat_solver_solve(s,lits,lits+n,1000,0,0,0);
  fprintf(o,"%d,%d,%d,%.9f\n",id,res,sat_solver_nconflicts(s)-conf,now()-start); fflush(o);
  if(m && res==l_True) {
   fprintf(m,"{\"query\":%d,\"values\":[",id);
   for(j=0;j<np;j++) {
    CHECK(s->model[vars[j]]==l_True || s->model[vars[j]]==l_False);
    fprintf(m,"%s%d",j?",":"",sat_solver_var_value(s,vars[j]));
   }
   fprintf(m,"]}\n"); fflush(m);
  }
 }
 free(vars); fclose(q); fclose(o); if(m) fclose(m); sat_solver_delete(s); return 0;
}
