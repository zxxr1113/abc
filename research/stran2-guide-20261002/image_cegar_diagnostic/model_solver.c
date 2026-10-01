/* Separate diagnostic helper. Existing query_solver.c is unchanged.
 * Inputs use ABC literals, including variable zero constrained false by CNF.
 * Only explicitly requested graph PI variables are projected into SAT models.
 */
#include "sat/bsat/satSolver.h"
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#define CHECK(c) do { if (!(c)) { fprintf(stderr,"invalid input at line %d\n",__LINE__); return 2; } } while(0)
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC,&t); return t.tv_sec+1e-9*t.tv_nsec; }
int main(int argc, char **argv) {
 FILE *f,*q,*v,*o,*m; int nv,nc,nq,np,i,j,n,id,res,conf; int *vars; lit lits[16]; sat_solver *s; double start;
 CHECK(argc==6); f=fopen(argv[1],"r"); q=fopen(argv[2],"r"); v=fopen(argv[3],"r"); o=fopen(argv[4],"w"); m=fopen(argv[5],"w"); CHECK(f&&q&&v&&o&&m);
 CHECK(fscanf(f,"%d%d",&nv,&nc)==2 && nv>0 && nc>0); s=sat_solver_new(); sat_solver_setnvars(s,nv);
 for(i=0;i<nc;i++) { CHECK(fscanf(f,"%d",&n)==1 && n>0 && n<=16); for(j=0;j<n;j++) CHECK(fscanf(f,"%d",lits+j)==1 && lits[j]>=0 && lits[j]<2*nv); CHECK(sat_solver_addclause(s,lits,lits+n)); }
 fclose(f); CHECK(fscanf(v,"%d",&np)==1 && np>=0 && np<nv); vars=(int *)malloc(sizeof(int)*(np+1)); CHECK(vars);
 for(i=0;i<np;i++) { CHECK(fscanf(v,"%d",vars+i)==1 && vars[i]>0 && vars[i]<nv); for(j=0;j<i;j++) CHECK(vars[j]!=vars[i]); }
 fclose(v); CHECK(fscanf(q,"%d",&nq)==1 && nq>=0); fprintf(o,"query,result,conflicts,wall_s\n"); fflush(o);
 for(i=0;i<nq;i++) {
  CHECK(fscanf(q,"%d%d",&id,&n)==2 && id==i && n>0 && n<=16); for(j=0;j<n;j++) CHECK(fscanf(q,"%d",lits+j)==1 && lits[j]>=0 && lits[j]<2*nv);
  conf=sat_solver_nconflicts(s); start=now(); res=sat_solver_solve(s,lits,lits+n,1000,0,0,0);
  fprintf(o,"%d,%d,%d,%.9f\n",id,res,sat_solver_nconflicts(s)-conf,now()-start); fflush(o);
  if(res==l_True) {
   fprintf(m,"{\"query\":%d,\"values\":[",id);
   for(j=0;j<np;j++) { CHECK(s->model[vars[j]]==l_True || s->model[vars[j]]==l_False); fprintf(m,"%s%d",j?",":"",sat_solver_var_value(s,vars[j])); }
   fprintf(m,"]}\n"); fflush(m);
  }
 }
 free(vars); fclose(q); fclose(o); fclose(m); sat_solver_delete(s); return 0;
}
