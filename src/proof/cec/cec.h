/**CFile****************************************************************

  FileName    [cec.h]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Combinational equivalence checking.]

  Synopsis    [External declarations.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - June 20, 2005.]

  Revision    [$Id: cec.h,v 1.00 2005/06/20 00:00:00 alanmi Exp $]

***********************************************************************/
 
#ifndef ABC__aig__cec__cec_h
#define ABC__aig__cec__cec_h


////////////////////////////////////////////////////////////////////////
///                          INCLUDES                                ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                         PARAMETERS                               ///
////////////////////////////////////////////////////////////////////////



ABC_NAMESPACE_HEADER_START


////////////////////////////////////////////////////////////////////////
///                         BASIC TYPES                              ///
////////////////////////////////////////////////////////////////////////

// dynamic SAT parameters
typedef struct Cec_ParSat_t_ Cec_ParSat_t;
struct Cec_ParSat_t_
{
    int              SolverType;    // SAT solver type
    int              nBTLimit;      // conflict limit at a node
    int              nSatVarMax;    // the max number of SAT variables
    int              nCallsRecycle; // calls to perform before recycling SAT solver
    int              fNonChrono;    // use non-chronological backtracling (for circuit SAT only)
    int              fPolarFlip;    // flops polarity of variables
    int              fCheckMiter;   // the circuit is the miter
//    int              fFirstStop;    // stop on the first sat output
    int              fLearnCls;     // perform clause learning
    int              fSaveCexes;    // saves counter-examples
    int              fVerbose;      // verbose stats
};

// simulation parameters
typedef struct Cec_ParSim_t_ Cec_ParSim_t;
struct Cec_ParSim_t_ 
{
    int              nWords;        // the number of simulation words
    int              nFrames;       // the number of simulation frames
    int              nRounds;       // the number of simulation rounds
    int              nNonRefines;   // the max number of rounds without refinement
    int              TimeLimit;     // the runtime limit in seconds
    int              fDualOut;      // miter with separate outputs
    int              fCheckMiter;   // the circuit is the miter
//    int              fFirstStop;    // stop on the first sat output
    int              fSeqSimulate;  // performs sequential simulation
    int              fLatchCorr;    // consider only latch outputs
    int              fConstCorr;    // consider only constants
    int              fVeryVerbose;  // verbose stats
    int              fVerbose;      // verbose stats
};

// semiformal parameters
typedef struct Cec_ParSmf_t_ Cec_ParSmf_t;
struct Cec_ParSmf_t_
{
    int              nWords;        // the number of simulation words
    int              nRounds;       // the number of simulation rounds
    int              nFrames;       // the max number of time frames
    int              nNonRefines;   // the max number of rounds without refinement
    int              nMinOutputs;   // the min outputs to accumulate
    int              nBTLimit;      // conflict limit at a node
    int              TimeLimit;     // the runtime limit in seconds
    int              fDualOut;      // miter with separate outputs
    int              fCheckMiter;   // the circuit is the miter
//    int              fFirstStop;    // stop on the first sat output
    int              fVerbose;      // verbose stats
};

// combinational SAT sweeping parameters
typedef struct Cec_ParFra_t_ Cec_ParFra_t;
struct Cec_ParFra_t_
{
    int              jType;         // solver type
    int              nWords;        // the number of simulation words
    int              nRounds;       // the number of simulation rounds
    int              nItersMax;     // the maximum number of iterations of SAT sweeping
    int              nBTLimit;      // conflict limit at a node
    int              nBTLimitPo;    // conflict limit at an output
    int              TimeLimit;     // the runtime limit in seconds
    int              nLevelMax;     // restriction on the level nodes to be swept
    int              nDepthMax;     // the depth in terms of steps of speculative reduction
    int              nCallsRecycle; // calls to perform before recycling SAT solver
    int              nSatVarMax;    // the max number of SAT variables
    int              nGenIters;     // pattern generation iterations
    int              fRewriting;    // enables AIG rewriting
    int              fCheckMiter;   // the circuit is the miter
//    int              fFirstStop;    // stop on the first sat output
    int              fDualOut;      // miter with separate outputs
    int              fColorDiff;    // miter with separate outputs
    int              fSatSweeping;  // enable SAT sweeping
    int              fRunCSat;      // enable another solver
    int              fUseCones;     // use cones
    int              fUseOrigIds;   // enable recording of original IDs
    int              fVeryVerbose;  // verbose stats
    int              fVerbose;      // verbose stats
    int              iOutFail;      // the failed output
    int              fBMiterInfo;   // printing BMiter information
    int              nPO;           // number of po in original design given a bmiter
    char *           pDumpName;     // file name to dump statistics
};

// combinational equivalence checking parameters
typedef struct Cec_ParCec_t_ Cec_ParCec_t;
struct Cec_ParCec_t_
{
    int              nBTLimit;      // conflict limit at a node
    int              TimeLimit;     // the runtime limit in seconds
//    int              fFirstStop;    // stop on the first sat output
    int              fUseSmartCnf;  // use smart CNF computation
    int              fRewriting;    // enables AIG rewriting
    int              fNaive;        // performs naive SAT-based checking
    int              fUseOrigIds;   // enable recording of original IDs 
    int              fSilent;       // print no messages
    int              fVeryVerbose;  // verbose stats
    int              fVerbose;      // verbose stats
    int              iOutFail;      // the number of failed output
    const char *     pNameSpec;     // name of the first (spec) network
    const char *     pNameImpl;     // name of the second (impl) network
    Vec_Ptr_t *      vNamesIn;      // input names of the first network
};

// Optional aggregate profiling for one or more correspondence calls.  All
// time fields use Abc_ClockHr() ticks (nanoseconds), rather than clock().
// The SAT/UNSAT/UNKNOWN counters below describe the internal SRM obligations
// seen by &scorr; they are intentionally distinct from a caller's final
// transaction outcome.
typedef struct Cec_ProfCor_t_ Cec_ProfCor_t;
struct Cec_ProfCor_t_
{
    abctime          timeClasses;   // class discovery + base + induction
    abctime          timeInit;      // simulation/class initialization
    abctime          timeBmc;       // complete reset/base phase
    abctime          timeBmcSrm;    // base-phase SRM construction
    abctime          timeBmcSat;    // base-phase solver wall time
    abctime          timeBmcSetup;  // solver/CNF setup within base phase
    abctime          timeBmcSolve;  // per-obligation solving within base phase
    abctime          timeBmcSim;    // base CEX resimulation/refinement
    abctime          timeInd;       // complete inductive refinement loop
    abctime          timeIndSrm;    // inductive SRM construction
    abctime          timeIndSat;    // inductive solver wall time
    abctime          timeIndSetup;  // solver/CNF setup within induction
    abctime          timeIndSolve;  // per-obligation solving within induction
    abctime          timeIndSim;    // inductive CEX resimulation/refinement
    abctime          timeReduce;    // final Gia_ManCorrReduce/cleanup
    long long        nBmcUnsat;     // internally discharged base obligations
    long long        nBmcSat;       // base obligations with counterexamples
    long long        nBmcUnknown;   // base obligations hitting proof limits
    long long        nIndUnsat;     // internally discharged step obligations
    long long        nIndSat;       // step obligations with counterexamples
    long long        nIndUnknown;   // step obligations hitting proof limits
    long long        nCexReal;      // SAT records carrying assignments
    long long        nCexTrivial;   // structurally constant-one obligations
    long long        nCexFail;      // timeout/failure records
    long long        nConfUsed;     // exact conflicts/backtracks consumed
    int              nConfStops;    // calls stopped by the total conflict cap
    int              nCalls;        // Cec_ManLSCorrespondenceClasses calls
    int              nBmcRounds;    // base SRMs built
    int              nIndRounds;    // inductive SRMs built
};

// sequential register correspodence parameters
typedef struct Cec_ParCor_t_ Cec_ParCor_t;
struct Cec_ParCor_t_
{
    int              nWords;        // the number of simulation words
    int              nRounds;       // the number of simulation rounds
    int              nFrames;       // the number of time frames
    int              nPrefix;       // the number of time frames in the prefix
    int              nBTLimit;      // conflict limit at a node
    int              nConfTotal;    // total conflicts across this correspondence call (0 = unlimited)
    long long        nConfUsed;     // output: exact conflicts/backtracks consumed
    int              fConfStop;     // output: total conflict cap was reached
    int              fIncomplete;   // output: correspondence stopped before convergence
    int              fCompleted;    // output: standard base+induction refinement converged
    int              nRoundsDone;   // output: completed induction refinement rounds
    int              nProcs;        // the number of processes
    int              nPartSize;     // the partition size
    int              nLevelMax;     // (scorr only) the max number of levels
    int              nStepsMax;     // (scorr only) the max number of induction steps
    int              nLimitMax;     // (scorr only) stop after this many iterations if little or no improvement
    int              nIncrFallbackPct; // (-i) fall back to full SRM when active pairs exceed this percent
    int              nDynSrmRebuildPct; // (-D) cold-rebuild when active pairs exceed this percent
    int              nDynSrmCompactMult; // (-D) cold-compact when core exceeds this multiple of reset size
    int              fLatchCorr;    // consider only latch outputs
    int              fConstCorr;    // consider only constants
    int              fUseRings;     // use rings
    int              fMakeChoices;  // use equilvaences as choices
    int              fUseCSat;      // use circuit-based solver
//    int              fFirstStop;    // stop on the first sat output
    int              fUseSmartCnf;  // use smart CNF computation
    int              fStopWhenGone; // quit when PO is not a candidate constant
    int              fIncremental;  // active-list/TFO-triggered reproof in main loop
    int              fIncrOracle;   // unbounded shadow SAT for pairs skipped by -i
    int              fIncrSim;      // persistent CEX-TFO-only resimulation after SAT
    int              fDynSrm;       // persistent dynamic SRM and true-unroll resimulation
    int              fDynSrmNoAdapt;// disable adaptive cold-rebuilds in DynSRM
    int              fUseTas;       // use TAS (vs CBS) for persistent solving (-D)
    int              fBmcTasAdaptive;// use guarded CBS-first/TAS-rescue policy in BMC
    int              fKissatCert;   // strictly audit final base+step obligations with Kissat
    int              fSkipFailResim;// skip resim in rounds with no real CEX (only timeout/fail)
    int              fVerifyResim;  // (-V) oracle: check incremental resim values vs full sweep
    int              fVerboseFlops; // verbose stats
    int              fVeryVerbose;  // verbose stats
    int              fVerbose;      // verbose stats
    Cec_ProfCor_t *  pProfile;      // optional aggregate phase profiling
    // callback
    void *           pData;
    void *           pFunc;
};

// sequential ODC synthesis parameters (research prototype)
typedef struct Cec_ParSodc_t_ Cec_ParSodc_t;
struct Cec_ParSodc_t_
{
    int              nFrames;       // induction depth used by scorr
    int              nConfLimit;    // SAT conflict limit per node
    int              nStepsMax;     // maximum scorr refinement rounds
    int              nCandMax;      // maximum number of candidate proofs
    int              nDivsMax;      // preceding AND divisors tried per fanin
    int              nChangesMax;   // maximum accepted transformations
    int              fUseScorr;     // run ordinary scorr before/after rewriting
    int              fVerbose;      // verbose output
};

// sequential register correspodence parameters
typedef struct Cec_ParChc_t_ Cec_ParChc_t;
struct Cec_ParChc_t_
{
    int              nWords;        // the number of simulation words
    int              nRounds;       // the number of simulation rounds
    int              nBTLimit;      // conflict limit at a node
    int              fUseRings;     // use rings
    int              fUseCSat;      // use circuit-based solver
    int              fVeryVerbose;  // verbose stats
    int              fVerbose;      // verbose stats
};

// sequential synthesis parameters
typedef struct Cec_ParSeq_t_ Cec_ParSeq_t;
struct Cec_ParSeq_t_
{
    int              fUseLcorr;     // enables latch correspondence
    int              fUseScorr;     // enables signal correspondence
    int              nBTLimit;      // (scorr/lcorr) conflict limit at a node
    int              nFrames;       // (scorr/lcorr) the number of timeframes
    int              nLevelMax;     // (scorr only) the max number of levels
    int              fConsts;       // (scl only) merging constants
    int              fEquivs;       // (scl only) merging equivalences
    int              fUseMiniSat;   // enables MiniSat in lcorr/scorr
    int              nMinDomSize;   // the size of minimum clock domain
    int              fVeryVerbose;  // verbose stats
    int              fVerbose;      // verbose stats
};

// CEC SimGen parameters
typedef struct Cec_ParSimGen_t_ Cec_ParSimGen_t;
struct Cec_ParSimGen_t_
{
    int              fVerbose;          // verbose flag
    int              fVeryVerbose;      // verbose flag
    int              expId;             // experiment ID for SimGen
    int              bitwidthOutgold;   // bitwidth of the output gold
    int              nSimWords;       // number of words in a round of random simulation
    int              nMaxIter;          // maximum number of rounds of random simulation
    char *           outGold;           // data containing outgold
    float            timeOutSim;        // timeout for simulation
    int              fUseWatchlist;     // use watchlist
    float            fImplicationTime;  // time spent in implication
    int              nImplicationExecution; // number of times implication was executed
    int              nImplicationSuccess; // number of times implication was successful
    int              nImplicationTotalChecks; // number of times implication was checked
    int              nImplicationSuccessChecks; // number of times implication was successful
    char *           pFileName;         // file name to dump simulation vectors
};

////////////////////////////////////////////////////////////////////////
///                      MACRO DEFINITIONS                           ///
////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
///                    FUNCTION DECLARATIONS                         ///
////////////////////////////////////////////////////////////////////////

/*=== cecCec.c ==========================================================*/
extern int           Cec_ManVerify( Gia_Man_t * p, Cec_ParCec_t * pPars );
extern int           Cec_ManVerifyTwo( Gia_Man_t * p0, Gia_Man_t * p1, int fVerbose );
extern int           Cec_ManVerifyTwoInv( Gia_Man_t * p0, Gia_Man_t * p1, int fVerbose );
extern int           Cec_ManVerifySimple( Gia_Man_t * p );
/*=== cecChoice.c ==========================================================*/
extern Gia_Man_t *   Cec_ManChoiceComputation( Gia_Man_t * pAig, Cec_ParChc_t * pPars );
/*=== cecCorr.c ==========================================================*/
extern int           Cec_ManLSCorrespondenceClasses( Gia_Man_t * pAig, Cec_ParCor_t * pPars );
extern Gia_Man_t *   Cec_ManLSCorrespondence( Gia_Man_t * pAig, Cec_ParCor_t * pPars );
extern void          Cec_ManSodcSetDefaultParams( Cec_ParSodc_t * pPars );
extern Gia_Man_t *   Cec_ManSodcSynthesis( Gia_Man_t * pAig, Cec_ParSodc_t * pPars );

// Sequential Direct root-resubstitution parameters.
typedef struct Cec_ParTran_t_ Cec_ParTran_t;
struct Cec_ParTran_t_
{
    int              nFrames;       // BMC/induction depth in the scorr oracle
    int              nBTLimit;      // conflict limit per proof obligation
    int              nStepsMax;     // scorr induction refinement limit
    int              nConstrMax;    // TFI depth used to collect local divisors (0 = complete TFI)
    int              nConstrBaseMax;// physical nodes in the local divisor pool (0 = all)
    int              nDepNodesMax;  // maximum AIG nodes in a dependency recipe (1..100)
    int              nGainMin;      // minimum local structural gain admitted to discovery
    int              nSimWords;     // 64-bit words per reachable simulation frame
    int              nSimFrames;    // random reset-reachable frames per signature batch
    int              nRootWaves;    // distinct candidate frontiers on one immutable snapshot
    int              nRootConstrTop;// canonical Build candidates retained per root (1..64)
    int              nCombBTLimit;  // root CBS conflict limit per cube
    int              nFreeWords;    // 64-bit independent PI/RO words for combination screening
    int              nFreeCexMax;   // CBS free-state counterexamples retained per proof batch
    int              nHardConfTotal;// whole-miter shadow-audit conflict cap
    int              fUseExisting;  // enable exact earlier-literal candidates
    int              fUseMffcDivs;  // allow exact-MFFC internal nodes in the root divisor pool
    int              fUseConstr;    // enable dependency-function resub recipes
    int              fUseCbsMultiLit;// root CBS: direct literal cubes vs constructed XOR query
    int              fRootExhaustive;// disable the local-gain discovery gate
    int              fUseFreeSim;   // screen/CEGIS CBS candidates with independent PI/RO signatures
    int              fSeqAllCands;  // root SEQ mode: 0=top-1, 1=all canonical candidates
    int              fShadow;       // whole-miter shadow audit for local proofs
    int              fProfile;      // print phase and target-gate profiles
};
extern void          Cec_ManTranSetDefaultParams( Cec_ParTran_t * pPars );
extern Gia_Man_t *   Cec_ManSequentialTransduction( Gia_Man_t * pAig, Cec_ParTran_t * pPars );
/*=== cecCore.c ==========================================================*/
extern void          Cec_ManSatSetDefaultParams( Cec_ParSat_t * p );
extern void          Cec_ManSimSetDefaultParams( Cec_ParSim_t * p );
extern void          Cec_ManSmfSetDefaultParams( Cec_ParSmf_t * p );
extern void          Cec_ManFraSetDefaultParams( Cec_ParFra_t * p );
extern void          Cec_ManCecSetDefaultParams( Cec_ParCec_t * p );
extern void          Cec_ManCorSetDefaultParams( Cec_ParCor_t * p );
extern void          Cec_ManChcSetDefaultParams( Cec_ParChc_t * p );
extern Gia_Man_t *   Cec_ManSatSweeping( Gia_Man_t * pAig, Cec_ParFra_t * pPars, int fSilent );
extern Gia_Man_t *   Cec_ManSatSolving( Gia_Man_t * pAig, Cec_ParSat_t * pPars, int f0Proved );
extern void          Cec_ManSimulation( Gia_Man_t * pAig, Cec_ParSim_t * pPars );
/*=== cecSeq.c ==========================================================*/
extern int           Cec_ManSeqResimulateCounter( Gia_Man_t * pAig, Cec_ParSim_t * pPars, Abc_Cex_t * pCex );
extern int           Cec_ManSeqSemiformal( Gia_Man_t * pAig, Cec_ParSmf_t * pPars );
extern int           Cec_ManCheckNonTrivialCands( Gia_Man_t * pAig );
/*=== cecSynth.c ==========================================================*/
extern int           Cec_SeqReadMinDomSize( Cec_ParSeq_t * p );
extern int           Cec_SeqReadVerbose( Cec_ParSeq_t * p );
extern void          Cec_SeqSynthesisSetDefaultParams( Cec_ParSeq_t * pPars );
extern int           Cec_SequentialSynthesisPart( Gia_Man_t * p, Cec_ParSeq_t * pPars );



ABC_NAMESPACE_HEADER_END



#endif

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////
