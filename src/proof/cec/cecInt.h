/**CFile****************************************************************

  FileName    [cecInt.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Combinational equivalence checking.]

  Synopsis    [External declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: cecInt.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/
 
#ifndef ABC__aig__cec__cecInt_h
#define ABC__aig__cec__cecInt_h


////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

#include "sat/bsat/satSolver.h"
#include "sat/glucose2/AbcGlucose2.h"
#include "misc/bar/bar.h"
#include "aig/gia/gia.h"
#include "cec.h"

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////



ABC_NAMESPACE_HEADER_START


////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

// simulation pattern manager
typedef struct Cec_ManPat_t_ Cec_ManPat_t;
struct Cec_ManPat_t_
{
    Vec_Int_t *      vPattern1;      // pattern in terms of primary inputs
    Vec_Int_t *      vPattern2;      // pattern in terms of primary inputs
    Vec_Str_t *      vStorage;       // storage for compressed patterns
    int              iStart;         // position in the array where recent patterns begin
    int              nPats;          // total number of recent patterns
    int              nPatsAll;       // total number of all patterns
    int              nPatLits;       // total number of literals in recent patterns
    int              nPatLitsAll;    // total number of literals in all patterns
    int              nPatLitsMin;    // total number of literals in minimized recent patterns
    int              nPatLitsMinAll; // total number of literals in minimized all patterns
    int              nSeries;        // simulation series
    int              fVerbose;       // verbose stats
    // runtime statistics
    abctime          timeFind;       // detecting the pattern  
    abctime          timeShrink;     // minimizing the pattern
    abctime          timeVerify;     // verifying the result of minimisation
    abctime          timeSort;       // sorting literals 
    abctime          timePack;       // packing into sim info structures 
    abctime          timeTotal;      // total runtime  
    abctime          timeTotalSave;  // total runtime for saving  
};

// SAT solving manager
typedef struct Cec_ManSat_t_ Cec_ManSat_t;
struct Cec_ManSat_t_
{
    // parameters
    Cec_ParSat_t *   pPars;          
    // AIGs used in the package
    Gia_Man_t *      pAig;           // the AIG whose outputs are considered
    Vec_Int_t *      vStatus;        // status for each output
    // SAT solving
    sat_solver *     pSat;           // recyclable SAT solver (MiniSAT)
    bmcg2_sat_solver*pSat2;          // recyclable SAT solver (Glucose)
    int              nSatVars;       // the counter of SAT variables
    int *            pSatVars;       // mapping of each node into its SAT var
    Vec_Ptr_t *      vUsedNodes;     // nodes whose SAT vars are assigned
    int              nRecycles;      // the number of times SAT solver was recycled
    int              nCallsSince;    // the number of calls since the last recycle
    Vec_Ptr_t *      vFanins;        // fanins of the CNF node
    // counter-examples
    Vec_Int_t *      vCex;           // the latest counter-example
    Vec_Int_t *      vVisits;        // temporary array for visited nodes  
    // SAT calls statistics
    int              nSatUnsat;      // the number of proofs
    int              nSatSat;        // the number of failure
    int              nSatUndec;      // the number of timeouts
    int              nSatTotal;      // the number of calls
    int              nCexLits;
    // conflicts
    int              nConfUnsat;     // conflicts in unsat problems
    int              nConfSat;       // conflicts in sat problems
    int              nConfUndec;     // conflicts in undec problems
    // runtime stats
    int              timeSatUnsat;   // unsat
    int              timeSatSat;     // sat
    int              timeSatUndec;   // undecided
    int              timeTotal;      // total runtime
};

// combinational simulation manager
typedef struct Cec_ManSim_t_ Cec_ManSim_t;
struct Cec_ManSim_t_
{
    // parameters
    Gia_Man_t *      pAig;           // the AIG to be used for simulation
    Cec_ParSim_t *   pPars;          // simulation parameters 
    int              nWords;         // the number of simulation words
    // recycable memory
    int *            pSimInfo;       // simulation information offsets
    unsigned *       pMems;          // allocated simulaton memory
    int              nWordsAlloc;    // the number of allocated entries
    int              nMems;          // the number of used entries  
    int              nMemsMax;       // the max number of used entries 
    int              MemFree;        // next free entry
    int              nWordsOld;      // the number of simulation words after previous relink
    // internal simulation info
    Vec_Ptr_t *      vCiSimInfo;     // CI simulation info  
    Vec_Ptr_t *      vCoSimInfo;     // CO simulation info  
    // counter examples
    void **          pCexes;         // counter-examples for each output
    int              iOut;           // first failed output
    int              nOuts;          // the number of failed outputs
    Abc_Cex_t *      pCexComb;       // counter-example for the first failed output
    Abc_Cex_t *      pBestState;     // the state that led to most of the refinements
    // scoring simulation patterns
    int *            pScores;        // counters of refinement for each pattern
    // temporaries
    Vec_Int_t *      vClassOld;      // old class numbers
    Vec_Int_t *      vClassNew;      // new class numbers
    Vec_Int_t *      vClassTemp;     // temporary storage
    Vec_Int_t *      vRefinedC;      // refined const reprs
};

// combinational simulation manager
typedef struct Cec_ManFra_t_ Cec_ManFra_t;
struct Cec_ManFra_t_
{
    // parameters
    Gia_Man_t *      pAig;           // the AIG to be used for simulation
    Cec_ParFra_t *   pPars;          // SAT sweeping parameters
    // simulation patterns
    Vec_Int_t *      vXorNodes;      // nodes used in speculative reduction
    int              nAllProved;     // total number of proved nodes
    int              nAllDisproved;  // total number of disproved nodes
    int              nAllFailed;     // total number of failed nodes
    int              nAllProvedS;    // total number of proved nodes
    int              nAllDisprovedS; // total number of disproved nodes
    int              nAllFailedS;    // total number of failed nodes
    // runtime stats
    abctime          timeSim;        // unsat
    abctime          timePat;        // unsat
    abctime          timeSat;        // sat
    abctime          timeTotal;      // total runtime
};

// incremental active-list manager for &scorr -i
typedef struct Cec_IncrMgr_t_ Cec_IncrMgr_t;
struct Cec_IncrMgr_t_
{
    Gia_Man_t *  pAig;            // host AIG (immutable across iterations)
    int          nFrames;         // unrolling depth used by the SRM builder
    int          nObjs;           // cached Gia_ManObjNum(pAig)
    Vec_Int_t *  vReprPrev;       // snapshot of pReprs from previous round
    Vec_Int_t *  vNextPrev;       // snapshot of pNexts from previous round
    Vec_Int_t *  vSeeds;          // repr-change TFO seeds
    Vec_Int_t *  vTfoNodes;       // ids currently in TFO (for fast clearing)
    int *        pTfoMark;        // dense mark array, size = nObjs
    Vec_Int_t *  vAliasHeads;     // repr -> first member using it in the SRM
    Vec_Int_t *  vAliasNext;      // next member with the same representative
    Vec_Int_t *  vBfsCur;         // BFS frontier for current frame
    Vec_Int_t *  vBfsNext;        // BFS frontier carried to next frame
    int          fOwnsFanout;     // 1 if we built static fanout (must free)
};

typedef enum Cec_IncrEmitMode_t_
{
    CEC_EMIT_ALL,
    CEC_EMIT_ACTIVE,
    CEC_EMIT_SKIPPED
} Cec_IncrEmitMode_t;

// CEX-diagnosis and split-TFO simulation manager for &scorr -I.
// Each failed SRM output is traced through the speculative TFI assumptions
// used to build it.  Host-AIG values under the current packed CEX batch identify
// the assumptions that are actually false.  Only real class splits seed the
// subsequent frame-aware TFO search for additional simulation refinements.
//
// Keying uses key = frame*nObjs + objId.  pVal layout:
//   pVal[(frame * nObjs + objId) * nWords + w]
typedef struct Cec_SeedSim_t_ Cec_SeedSim_t;
struct Cec_SeedSim_t_
{
    Gia_Man_t *  pAig;            // host AIG (immutable across iterations)
    int          nFrames;         // total unrolling depth used by resim
    int          iSeedFrame;       // frame where SAT proved the endpoint pair
    int          nObjs;           // cached Gia_ManObjNum(pAig)
    int          nPis;            // cached Gia_ManPiNum(pAig)
    int          nRegs;           // cached Gia_ManRegNum(pAig)
    int          nWords;          // sim words per key (= pSim->pPars->nWords)
    int          fInitialized;     // at least one standard full sweep completed
    // Dense value storage.  Data lanes are current only when pEvalMark carries
    // nEvalVersion.  Bit 0 is the deterministic phase anchor established by a
    // full sweep and is preserved while current CEX lanes are recomputed.
    unsigned *   pVal;            // size = (size_t)nFrames * nObjs * nWords
    unsigned *   pEvalMask;       // lanes computed in the current value version
    unsigned *   pActiveMask;     // packed real-CEX lanes participating in refinement
    unsigned *   pFoundMask;      // CEX lanes explained by a real host-AIG split
    unsigned *   pDiffMask;       // nWords scratch for signature differences
    unsigned *   pTempMask;       // nWords scratch
    // Dense per-key state.
    int *        pMark;           // split-TFO visited stamp, size = nFrames * nObjs
    int *        pSpecMark;       // sparse speculative-mask record index plus one
    int *        pDiagMark;       // sparse diagnosis record index plus one
    int *        pSplitMark;      // real-split worklist stamp
    int *        pProcessMark;    // split-TFO key already refined stamp
    int *        pEvalMark;       // current-input value version stamp
    int          nMarkVersion;
    int          nSplitVersion;
    int          nProcessVersion;
    int          nEvalVersion;
    int          nSpecKeys;       // unrolled keys visited by speculative diagnosis
    int          nEvalKeys;       // keys evaluated from current inputs this batch
    Vec_Int_t *  vDiagPairs;      // failed host pairs as triples (obj0, obj1, bit)
    Vec_Int_t *  vSpecKeys;       // sparse speculative-TFI keys
    Vec_Int_t *  vSpecMasks;      // flat [spec record][word] lane masks
    Vec_Int_t *  vDiagKeys;       // sparse speculative assumptions/failed endpoints
    Vec_Int_t *  vDiagRoots;      // original class root for each diagnosis record
    Vec_Int_t *  vDiagMasks;      // flat [diagnosis record][word] lane masks
    Vec_Int_t *  vSplitKeys;      // nodes in classes actually split by current CEX
    Vec_Int_t *  vDirtyKeys;      // keys reached by split-driven TFO
    Vec_Int_t *  vWaveKeys;       // newly reached TFO keys awaiting refinement
    Vec_Int_t *  vQueue;          // split-TFO BFS frontier
    Vec_Ptr_t *  vSimInfo;        // reusable full-simulation CI storage
    Vec_Ptr_t *  vBatchInfo;      // non-owning current packed CEX input vectors
    // Class-refinement scratch.
    int *        pRootMark;       // per-objId "root already queued" stamp
    int          nRootVersion;
    Vec_Int_t *  vDirtyRoots;
    Vec_Int_t *  vConstRefined;
    Vec_Int_t *  vClassAll;
    Vec_Int_t *  vClassOld;
    Vec_Int_t *  vClassNew;
    unsigned *   pPhase0;         // nWords of 0 (phase-0 vector, used by refine)
    unsigned *   pPhase1;         // nWords of ~0 (phase-1 vector)
    int          fOwnsFanout;     // 1 if we built static fanout (must free)
    // Profile counters (reset per resim call)
    int          nBatchLocal;     // rounds handled by local TFO sim
    int          nBatchFull;      // rounds that fell back to full sweep
    int          nMaxDirty;       // largest TFO/evaluated closure across this call
};

// Fall back when diagnosis/TFO/evaluation exceeds this fraction of the unrolled AIG.
#define CEC_SEEDSIM_FRAC_NUM 3
#define CEC_SEEDSIM_FRAC_DEN 5

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== cecCorr.c ============================================================*/
extern void                 Cec_ManRefinedClassPrintStats( Gia_Man_t * p, Vec_Str_t * vStatus, int iIter, abctime Time );
extern int                  Gia_ManCorrSpecReal( Gia_Man_t * pNew, Gia_Man_t * p, Gia_Obj_t * pObj, int f, int nPrefix );
extern void                 Gia_ManCorrSpecReduce_rec( Gia_Man_t * pNew, Gia_Man_t * p, Gia_Obj_t * pObj, int f, int nPrefix );
/* &scorr per-proof profiling counters: defined in cecCorr.c, written by the    */
/* SAT/CSAT miter solvers, reset+read by the &scorr loop. All times in ns.      */
extern int                  Cec_ScorrProfOn;     // master enable (gates all profiling work)
extern int                  Cec_ScorrProfCalls;  // # of per-PO solve calls in the last miter
extern abctime              Cec_ScorrProfSetup;  // solver alloc + AIG prep before the PO loop
extern abctime              Cec_ScorrProfSolve;  // summed over every per-PO solve call
extern abctime              Cec_ScorrProfMax;    // slowest single per-PO solve call
/*=== cecCorrIncr.c ============================================================*/
extern Cec_IncrMgr_t *      Cec_IncrMgrAlloc( Gia_Man_t * pAig, int nFrames );
extern void                 Cec_IncrMgrFree( Cec_IncrMgr_t * p );
extern void                 Cec_IncrMgrSnapshotClasses( Cec_IncrMgr_t * p );
extern int                  Cec_IncrMgrComputeSeeds( Cec_IncrMgr_t * p );
extern int                  Cec_IncrMgrCountNextChanges( Cec_IncrMgr_t * p );
extern int                  Cec_IncrMgrRingEdgeChanged( Cec_IncrMgr_t * p, int iPrev, int iObj );
extern void                 Cec_IncrMgrCountActivePairs( Cec_IncrMgr_t * p, int fRings, int * pTfoMark, int * pnTotal, int * pnActive );
extern void                 Cec_IncrMgrComputeTfo( Cec_IncrMgr_t * p );
extern Gia_Man_t *          Gia_ManCorrSpecReduce_Emit( Gia_Man_t * p, int nFrames, int fScorr, Vec_Int_t ** pvOutputs, int fRings, int * pTfoMark, Cec_IncrMgr_t * pIncr, Cec_IncrEmitMode_t Mode, Vec_Int_t ** pvOutLits );
extern Gia_Man_t *          Gia_ManCorrSpecReduceInit_Active( Gia_Man_t * p, int nFrames, int nPrefix, int fScorr, Vec_Int_t ** pvOutputs, int * pTfoMark );
/*=== cecCorrIncrSim.c ============================================================*/
extern Cec_SeedSim_t *      Cec_SeedSimAlloc( Gia_Man_t * pAig, int nFrames, int iSeedFrame, int nWords );
extern void                 Cec_SeedSimFree( Cec_SeedSim_t * p );
extern int                  Cec_SeedSimTryBatch( Cec_SeedSim_t * p, Cec_ManSim_t * pSim, Vec_Ptr_t * vSimInfo, Vec_Int_t * vOutputs, Vec_Int_t * vOutBits, int nFrames );
extern void                 Cec_SeedSimSaveFrameInputs( Cec_SeedSim_t * p, Vec_Ptr_t * vInfoCis, int Frame );
extern void                 Cec_SeedSimSaveFrameOutputs( Cec_SeedSim_t * p, Vec_Ptr_t * vInfoCos, int Frame );
extern void                 Cec_SeedSimFinishFull( Cec_SeedSim_t * p );
extern void                 Cec_SeedSimBeginCall( Cec_SeedSim_t * p );
extern int                  Cec_SeedSimNumLocal ( Cec_SeedSim_t * p );
extern int                  Cec_SeedSimNumFull  ( Cec_SeedSim_t * p );
extern int                  Cec_SeedSimNumDirty ( Cec_SeedSim_t * p );
extern int                  Cec_SeedSimNumKeys  ( Cec_SeedSim_t * p );
/*=== cecClass.c ============================================================*/
extern int                  Cec_ManSimClassRemoveOne( Cec_ManSim_t * p, int i );
extern void                 Cec_ManSimClassCreate( Gia_Man_t * p, Vec_Int_t * vClass );
extern int                  Cec_ManSimCompareEqual( unsigned * p0, unsigned * p1, int nWords );
extern int                  Cec_ManSimHashKey( unsigned * pSim, int nWords, int nTableSize );
extern int                  Cec_ManSimClassesPrepare( Cec_ManSim_t * p, int LevelMax );
extern int                  Cec_ManSimClassesRefine( Cec_ManSim_t * p );
extern int                  Cec_ManSimSimulateRound( Cec_ManSim_t * p, Vec_Ptr_t * vInfoCis, Vec_Ptr_t * vInfoCos );
extern int                  Cec_ManSimSimulateRoundSave( Cec_ManSim_t * p, Vec_Ptr_t * vInfoCis, Vec_Ptr_t * vInfoCos, unsigned * pSave );
/*=== cecIso.c ============================================================*/
extern int *                Cec_ManDetectIsomorphism( Gia_Man_t * p );
/*=== cecMan.c ============================================================*/
extern Cec_ManSat_t *       Cec_ManSatCreate( Gia_Man_t * pAig, Cec_ParSat_t * pPars );
extern void                 Cec_ManSatPrintStats( Cec_ManSat_t * p );
extern void                 Cec_ManSatStop( Cec_ManSat_t * p );
extern Cec_ManPat_t *       Cec_ManPatStart();
extern void                 Cec_ManPatPrintStats( Cec_ManPat_t * p );
extern void                 Cec_ManPatStop( Cec_ManPat_t * p );
extern Cec_ManSim_t *       Cec_ManSimStart( Gia_Man_t * pAig, Cec_ParSim_t *  pPars ); 
extern void                 Cec_ManSimStop( Cec_ManSim_t * p );  
extern Cec_ManFra_t *       Cec_ManFraStart( Gia_Man_t * pAig, Cec_ParFra_t *  pPars );  
extern void                 Cec_ManFraStop( Cec_ManFra_t * p );
/*=== cecPat.c ============================================================*/
extern void                 Cec_ManPatSavePattern( Cec_ManPat_t *  pPat, Cec_ManSat_t *  p, Gia_Obj_t * pObj );
extern void                 Cec_ManPatSavePatternCSat( Cec_ManPat_t * pMan, Vec_Int_t * vPat );
extern Vec_Ptr_t *          Cec_ManPatCollectPatterns( Cec_ManPat_t *  pMan, int nInputs, int nWords );
extern Vec_Ptr_t *          Cec_ManPatPackPatterns( Vec_Int_t * vCexStore, int nInputs, int nRegs, int nWordsInit );
/*=== cecSeq.c ============================================================*/
extern int                  Cec_ManSeqResimulate( Cec_ManSim_t * p, Vec_Ptr_t * vInfo );
extern int                  Cec_ManSeqResimulateSeed( Cec_ManSim_t * p, Vec_Ptr_t * vInfo, Cec_SeedSim_t * pSeed );
extern int                  Cec_ManSeqResimulateInfo( Gia_Man_t * pAig, Vec_Ptr_t * vSimInfo, Abc_Cex_t * pBestState, int fCheckMiter );
extern void                 Cec_ManSeqDeriveInfoInitRandom( Vec_Ptr_t * vInfo, Gia_Man_t * pAig, Abc_Cex_t * pCex );
extern int                  Cec_ManCountNonConstOutputs( Gia_Man_t * pAig );
extern int                  Cec_ManCheckNonTrivialCands( Gia_Man_t * pAig );
/*=== cecSolve.c ============================================================*/
extern int                  Cec_ObjSatVarValue( Cec_ManSat_t * p, Gia_Obj_t * pObj );
extern void                 Cec_ManSatSolve( Cec_ManPat_t * pPat, Gia_Man_t * pAig, Cec_ParSat_t * pPars, Vec_Int_t * vIdsOrig, Vec_Int_t * vMiterPairs, Vec_Int_t * vEquivPairs, int f0Proved );
extern void                 Cec_ManSatSolveCSat( Cec_ManPat_t * pPat, Gia_Man_t * pAig, Cec_ParSat_t * pPars );
extern Vec_Str_t *          Cec_ManSatSolveSeq( Vec_Ptr_t * vPatts, Gia_Man_t * pAig, Cec_ParSat_t * pPars, int nRegs, int * pnPats );
extern Vec_Int_t *          Cec_ManSatSolveMiter( Gia_Man_t * pAig, Cec_ParSat_t * pPars, Vec_Str_t ** pvStatus );
extern Vec_Int_t *          Cec_ManSatSolveMiterOutVals( Gia_Man_t * pAig, Cec_ParSat_t * pPars, Vec_Str_t ** pvStatus, Vec_Int_t * vOutLits, Vec_Int_t ** pvOutVals );
extern int                  Cec_ManSatCheckNode( Cec_ManSat_t * p, Gia_Obj_t * pObj );
extern int                  Cec_ManSatCheckNodeTwo( Cec_ManSat_t * p, Gia_Obj_t * pObj1, Gia_Obj_t * pObj2 );
extern void                 Cec_ManSavePattern( Cec_ManSat_t * p, Gia_Obj_t * pObj1, Gia_Obj_t * pObj2 );
extern Vec_Int_t *          Cec_ManSatReadCex( Cec_ManSat_t * p );
/*=== cecSolveG.c ============================================================*/
extern void                 CecG_ManSatSolve( Cec_ManPat_t * pPat, Gia_Man_t * pAig, Cec_ParSat_t * pPars, int f0Proved );
/*=== ceFraeep.c ============================================================*/
extern Gia_Man_t *          Cec_ManFraSpecReduction( Cec_ManFra_t * p );
extern int                  Cec_ManFraClassesUpdate( Cec_ManFra_t * p, Cec_ManSim_t * pSim, Cec_ManPat_t * pPat, Gia_Man_t * pNew );



ABC_NAMESPACE_HEADER_END



#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
