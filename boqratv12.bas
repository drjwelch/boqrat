********************************************************************************
REM  ***                        BOQRAT v1.2a                                 ***
********************************************************************************

********************************************************************************
REM  *** Calculates pr(m) given multi-choice section scores for a whole      ***
REM  *** class with correlation between pupils and also between sections     ***
REM  *** based on increasing difficulty.                                     ***
********************************************************************************

********************************************************************************
REM  *** Version History                                                     ***
REM  ***                                                                     ***
REM  *** v1.2a Changed alpha range                                           ***
REM  *** v1.2 Corrected final index of mp (limit is SECTIONS-2 not -1) in    ***
REM  ***      dimension and in use (in SETP_MP_...)                          ***
REM  ***      Corrected SETUP_FP to multiply pr(fi) correctly                ***
REM  ***                                                                     ***
REM  *** v1.1 First full version with command-line options                   ***
********************************************************************************

********************************************************************************
rem ***                      DEFINITIONS AND DECLARATIONS                    ***
********************************************************************************

REM  *** Declarations ***

defdbl a-z

REM  *** Hard coded values/limits ***
const STUDENTS = 40
const SECTIONS = 3
const QUESTIONS = 8
const CHOICES = 4
const FGRAIN = 10
const FMIN = 0.01
const FMAX = 0.91
const TRUE = 1
const VERY = 99
const FALSE = 0
const ALPHAMIN = 0.001
const ALPHAMAX = 10

rem *** Number of students read from file
dim N as integer

rem *** Student scores read from file
dim s(0 to STUDENTS-1, 0 to SECTIONS-1) as integer

rem *** Probability look-up tables
dim shared fact(0 to QUESTIONS) as double
dim shared likelihood(0 to QUESTIONS, 0 to QUESTIONS) as double
dim shared kp(0 to QUESTIONS, 0 to QUESTIONS, 0 to SECTIONS-1) as double
dim shared mp(0 to QUESTIONS, 0 to QUESTIONS, 0 to SECTIONS-2) as double
dim shared fp(0 to FGRAIN^3-1) as double
dim shared em(0 to SECTIONS-1) as integer

rem *** Parameter look-up table
rem ***     index 0              = alpha linking sectn 2 from 1,
rem ***     index 1              = alpha linking sectn 3 from 2, etc.
rem ***     index SECTIONS-1 + 0 = f for section 1,
rem ***     index SECTIONS-1 + 1 = f for section 2, etc.
dim shared parameters(0 to 2*SECTIONS-2) as double

rem *** Final results
dim bestpost(0 to (QUESTIONS+1)^SECTIONS-1) as double
dim mpost(0 to QUESTIONS*SECTIONS) as double
dim evidence as double
dim smean as double
dim svar as double

rem *** Intermediate results and counters
dim posterior(0 to (QUESTIONS+1)^SECTIONS-1) as double
dim ksum as double
dim prob as double
dim emax as double
dim bestf as integer
dim findex as integer
dim param as double
dim mprior as integer
dim marginalising as integer

rem *** File handles and flags
dim infile as string
dim outfile as string
dim verbose as integer

rem *** Loop variables
dim i as integer
dim j as integer
dim k as integer
dim m as integer

REM *** Function / sub declarations ***

declare function logfactorial(i as integer) as double
declare sub calc_em(m as integer)
declare sub setup_l
declare sub setup_kp
declare sub setup_mp_exp
declare sub setup_mp_lin
declare sub setup_fp

********************************************************************************
rem ***                              MAIN PROGRAM                            ***
********************************************************************************

rem *** Read command line options

if instr(command$,"-?") then
  print
  print"boqrat [-i filename] [-o filename] [-max] [-exp [-a1 alpha12] [-a2 alpha23]] [-v]"
  print"  -i filename	Specifies the input file name"
  print"  -o filename	Specifies the output file name"
  print"  -max		Selects maximisation over f (default: marginalises)"
  print"  -exp		Selects exponential m-prior (default: linear)"
  print"  -an alphann	Specifies value of alpha to use for section correlation"
  print"  -v		Verbose - prints input data and progress"
  print
  print"  Input  files must be CSV and have .csv appended if not specified"
  print"  Output files are CSV and are named '<inputfile>OUT.csv' if not specified"
  end
end if

verbose = FALSE
if instr(command$,"-v") then verbose = TRUE
if instr(command$,"-d") then verbose = VERY

mprior = FALSE
parameters(0) = 0.0
parameters(1) = 0.0
if instr(command$,"-exp") then
  mprior = TRUE
  i = instr(command$,"-a1")
  if (i<>0) then temp$=mid$(command$,i+3,instr(right$(command$,len(command$)-i-3)," "))
  parameters(0) = val(temp$)
  i = instr(command$,"-a2")
  if (i<>0) then temp$=mid$(command$,i+3,instr(right$(command$,len(command$)-i-3)," "))
  parameters(1) = val(temp$)
  if (parameters(0) < ALPHAMIN OR parameters(0) > ALPHAMAX) then input"Enter valid alpha12 > ";parameters(0)
  if (parameters(1) < ALPHAMIN OR parameters(1) > ALPHAMAX) then input"Enter valid alpha23 > ";parameters(1)
end if

marginalising = TRUE
if instr(command$,"-max") then
  marginalising = FALSE
end if

i = instr(command$,"-i")
if (i<>0) then infile$ = mid$(command$,i+3,instr(right$(command$,len(command$)-i-3)," "))
if (infile$="") then input "Type filename for data input (.csv is added) > ",infile$
if (right$(infile$,4)<>".csv") then infile$ = infile$ + ".csv"

i = instr(command$,"-o")
outfile$=left$(infile$,len(infile$)-4)+"out.csv"
if (i<>0) then outfile$ = mid$(command$,i+3,instr(right$(command$,len(command$)-i-3)," "))
if (right$(outfile$,4)<>".csv") then outfile$ = outfile$ + ".csv"

if (verbose = TRUE) then
  print "Infile        = ";infile$
  print "Mprior        = ";mprior
  print "Alpha12       = ";parameters(0)
  print "Alpha23       = ";parameters(1)
  print "Marginalising = ";marginalising
end if

rem *** Read in three section scores and prior information from keyboard ***
rem *** will read from command line in future

open infile$ for input as #1
input #1, N
for i = 0 to N-1
  if (verbose = TRUE) then print"Student ";i;" scores ";
  for j = 0 to SECTIONS-1
    input #1, s(i,j)
    if (verbose = TRUE) then print s(i,j);" ";
  next j
  if (verbose = TRUE) then print
next i
close #1

rem *** Set up table of factorials ***

for i = 0 to QUESTIONS
  fact(i) = logfactorial(i)
next i

rem *** Set up table of binomial likelihood values ***

setup_L

rem *** Set up tables for m-prior, either exponential or linear

if mprior = TRUE then setup_MP_exp else setup_MP_lin

rem *** Set up tables for f-prior

setup_FP

********************************************************************************
rem ***                              MAIN LOOP                               ***
********************************************************************************

rem *** Best evidence found so far is reset and bestpost() array is cleared ***
emax = 0.0
for m = 0 to (QUESTIONS+1)^SECTIONS-1
  bestpost(i) = 0.0
next m

rem *** Outer loop, findex, runs over values of f, the fall-off rate in pr(k)
for findex = 0 to FGRAIN^SECTIONS-1

rem *** Set f values in parameter table
  if (verbose = TRUE) then print "f = (";
  for i = 0 to SECTIONS-1
    parameters(i+SECTIONS-1)=(INT(findex/FGRAIN^i) MOD FGRAIN)*(FMAX-FMIN)/(FGRAIN-1)+FMIN
    if (verbose = TRUE AND findex MOD FGRAIN = 0) then
      print ;parameters(i+SECTIONS-1);
      if (i<>SECTIONS-1) then print ;", ";
    end if
  next i
  if (verbose = TRUE) then print ;")"

rem *** Evidence reset to zero for each set of f's
  evidence = 0.0

rem *** Set up tables for (k|mf) prior - must be re-done for each set of f's
  setup_KP

rem *** then multiply all these integrals together (they are separable)

rem *** Loop over all points in m-space
  for m = 0 to (QUESTIONS+1)^SECTIONS-1

rem *** Assign m-space co-ordinates being considered to array em()
    calc_EM(m)

rem *** Reset pr(m)=1 (not zero as it's under a product, not a sum)
    prob = 1.0

rem *** Loop over each section score (j) for each kid (i)
    for i = 0 to N-1
      for j = 0 to SECTIONS-1

rem *** Set k-sum value to zero then sum over all valid k's for this kid's section score
        ksum = 0.0
        for k = 0 to s(i,j)
          ksum = ksum + kp(em(j),k,j) * likelihood(k,s(i,j))
        next k

        prob = prob * ksum
      next j
    next i

rem *** Finally multiply by m-prior (one for each section)
rem *** First section m-prior is flat in [0,QUESTIONS]
    prob = prob / (QUESTIONS+1)
rem *** Other sections m-prior was pre-calculated into mp()
    for i = 1 to SECTIONS-1
      prob = prob * mp(em(i),em(i-1),i-1)
    next i

rem *** Multiply by f-prior
    prob = prob * fp(findex)

rem *** Recording and tracking - store posterior, and keep track of evidence
    posterior(m) = prob
    evidence = evidence + posterior(m)

  next m

rem *** If we are marginalising over f, then add this f's result to the final posterior
rem *** If we are maximising over f and this is the best set of f's so far, record posterior and details
  if (marginalising = TRUE) then
    for i = 0 to (QUESTIONS+1)^SECTIONS-1
      bestpost(i) = bestpost(i) + posterior(i)
    next i
    emax = emax + evidence
  else
    if (evidence > emax) then
      bestf = findex
      emax = evidence
      for i = 0 to (QUESTIONS+1)^SECTIONS-1
        bestpost(i) = posterior(i)
      next i
    end if
  end if

next findex

********************************************************************************
rem ***                            END MAIN LOOP                             ***
********************************************************************************

REM *** Prepare and write output datafile

if (verbose = TRUE) then print"Writing output to '";outfile$;"'"
open outfile$ for output as #1

rem *** Clear mpost() to receive posterior projected onto total m
for i = 0 to QUESTIONS*SECTIONS
  mpost(i) = 0.0
next i
rem *** Add-up cells for projected posterior while writing out full posterior
for m = 0 to (QUESTIONS+1)^SECTIONS-1
  calc_EM(m)
  j = 0
  for i = 0 to SECTIONS-1
    j = j + em(i)
    print #1, em(i);", ";
  next i
  mpost(j) = mpost(j) + bestpost(m)
  write #1, bestpost(m)/emax
next m
rem *** Write out projection
for m = 0 to QUESTIONS*SECTIONS
  write #1, m, mpost(m)/emax
next m

rem *** Write out run parameters
print #1, "Input datafile",infile$

print #1, "Exponential mp?",mprior
if mprior=1 then print #1, "Alpha values",parameters(0),parameters(1)

print #1, "Marginalising?",marginalising
if marginalising=0 then
  print #1, "Best f's"
  for i = 0 to SECTIONS-1
    param = (INT(bestf/FGRAIN^i) MOD FGRAIN)*(FMAX-FMIN)/(FGRAIN-1)+FMIN
    print #1, param
  next i
end if

print #1, "Evidence",emax

rem *** Finally calculate evidence of uncorrelated model - reuse variables emax and ksum
emax = 1.0
for i = 0 to N-1
  for j = 0 to SECTIONS-1
    ksum = 0.0
    for k = 0 to s(i,j)
      ksum = ksum + likelihood(k,s(i,j)) / 9.0
    next k
    emax = emax * ksum
  next j
rem  smean = smean + s(i,j)
rem  svar = svar + s(i,j)^2
next i

print #1, "Uncorr Model Evidence",emax
rem print #1, "Scores Mean",smean/N
rem print #1, "Scores Variance",svar/N - (smean/N)^2

close #1

end

********************************************************************************
rem ***                   FUNCTION AND SUB DEFINITIONS                       ***
********************************************************************************

********************************************************************************
rem ***                       FUNCTION LOGFACTORIAL                          ***
********************************************************************************

rem *** LOGFACTORIAL() ***
rem *** Calculates a table of log(x!) used by SETUP_L ***

function logfactorial(i as integer) as double

  dim temp as double
  dim j as integer

  temp = 0.0

  if i>1 then
    for j = 2 to i
      temp = temp + log(j)
    next j
  end if

  logfactorial = temp

end function

********************************************************************************
rem ***                         SUBROUTINE CALC_EM                           ***
********************************************************************************

rem *** CALC_EM(m) ***
rem *** Turns index m into a set of indices for each section ***
rem *** e.g. for 3 sections, turns m=106 into m1=7,m2=2,m3=1 (1x81 + 2x9 + 7)

SUB CALC_EM(m as integer)

  dim i as integer

  for i = 0 to SECTIONS-1
    em(i) = INT(m/((QUESTIONS+1)^i)) MOD (QUESTIONS+1)
  next i

END SUB

********************************************************************************
rem ***                         SUBROUTINE SETUP_L                           ***
********************************************************************************

rem *** SETUP_L ***
rem *** Pre-calculates binomial likelihood factors ***

SUB SETUP_L

  dim value as double
  dim k as integer
  dim s as integer

  for s = 0 to QUESTIONS
    for k = 0 to s
      value = fact(QUESTIONS-k) - fact(s-k) - fact(QUESTIONS-s)
      value = value + cdbl(QUESTIONS-s)*log(CHOICES-1) - cdbl(QUESTIONS-k)*log(CHOICES)
      likelihood(k,s) = exp(value)
    next k
  next s

END SUB

********************************************************************************
rem ***                         SUBROUTINE SETUP_KP                          ***
********************************************************************************

rem *** SETUP_KP ***
rem *** Pre-calculates (k|mf) prior ***

SUB SETUP_KP
  dim m as integer
  dim k as integer
  dim i as integer
  dim Zk as double

rem *** Table kp(m,k,f) = pr(k|m,f)/Zk
rem *** Inner loop over k twice; find Zk then complete kp values

  for i = 0 to SECTIONS-1
    for m = 0 to QUESTIONS
      Zk = 0.0
      for k = 0 to QUESTIONS
        kp(m,k,i) = parameters(SECTIONS-1+i)^cdbl(abs(m-k))
        Zk = Zk + kp(m,k,i)
      next k
      for k = 0 to QUESTIONS
        kp(m,k,i) = kp(m,k,i)/Zk
      next k
    next m
  next i

END SUB

********************************************************************************
rem ***                       SUBROUTINE SETUP_MP_EXP                        ***
********************************************************************************

rem *** SETUP_MP_EXP ***
rem *** Pre-calculates discretised pr(m,alpha) = pr(m|alpha)pr(alpha) prior
rem *** This version with EXPONENTIAL fall-off is controlled by ALPHA
rem *** If required you can manually maximise over alpha by running with
rem *** different settings in the allowed range

SUB SETUP_MP_EXP

  dim thism as integer
  dim lastm as integer
  dim Z as double
  dim i as integer

REM *** lastm is score in previous section (excluding max score=QUESTIONS - see later)
REM *** thism is score in this section
REM *** Z is the normalisation constant (analytic since it's just the sum of a GP)

for i = 0 to SECTIONS-2

  for lastm = 0 to QUESTIONS-1
rem formula doesn't fit on one line
    Z = (1.0 - exp((QUESTIONS+1)*cdbl(lastm-QUESTIONS)/parameters(i)))
    Z = Z / (1.0 - exp(cdbl(lastm-QUESTIONS)/parameters(i)))
    for thism = 0 to QUESTIONS
      mp(thism,lastm,i) = exp(cdbl(thism)*cdbl(lastm-QUESTIONS)/parameters(i)) / Z
    next thism
  next lastm

REM *** Deal with special case where lastm=QUESTIONS and prior is flat across thism

  for thism = 0 to QUESTIONS
    mp(thism,QUESTIONS,i) = 1.0 / (QUESTIONS+1)
  next thism

next i

rem *** Finally, multiply by alpha prior (analytic as it is just 1/alpha in the specified range)
  for thism = 0 to QUESTIONS
    for lastm = 0 to QUESTIONS
      for i = 0 to SECTIONS-2
        mp(thism,lastm,i) = mp(thism,lastm,i) / ( parameters(i) * log(ALPHAMAX/ALPHAMIN) )
      next i
    next lastm
  next thism

END SUB

********************************************************************************
rem ***                       SUBROUTINE SETUP_MP_LIN                        ***
********************************************************************************

rem *** SETUP_MP_LIN ***
rem *** Pre-calculates linear version of pr(m) prior
rem *** This version with LINEAR fall-off has no parameters

SUB SETUP_MP_LIN

  dim thism as integer
  dim lastm as integer
  dim Z as double
  dim i as integer
  dim limit as double

REM *** lastm is score in previous section (excluding max score=QUESTIONS - see later)
REM *** thism is score in this section
REM *** Z keeps a sum of this section probs to normalise

  for lastm = 0 to QUESTIONS-1
    Z = 0.0
    for thism = 0 to QUESTIONS
      limit = 0.5*QUESTIONS^2 / cdbl(QUESTIONS-lastm)
      if (thism<=limit) then mp(thism,lastm,0) = (1.0-thism/limit) else mp(thism,lastm,0) = 0.0
      Z = Z + mp(thism,lastm,0)
    next thism
    for thism = 0 to QUESTIONS
      mp(thism,lastm,0) = mp(thism,lastm,0) / Z
    next thism
  next lastm

REM *** Deal with special case where lastm=QUESTIONS and prior is flat across thism

  for thism = 0 to QUESTIONS
    mp(thism,QUESTIONS,0) = 1.0 / (QUESTIONS+1)
  next thism

rem *** Finally, copy mp(,,0) to mp(,,1) - the extra index is only used for exp decay prior
  for thism = 0 to QUESTIONS
    for lastm = 0 to QUESTIONS
      for i = 1 to SECTIONS-2
        mp(thism,lastm,i) = mp(thism,lastm,0)
      next i
    next lastm
  next thism

END SUB

********************************************************************************
rem ***                         SUBROUTINE SETUP_FP                          ***
********************************************************************************

rem *** SETUP_FP ***
rem *** Pre-calculates (f) prior ***

SUB SETUP_FP
  dim findex as integer
  dim i as integer
  dim tempf as double
  dim Zf as double

rem *** Table fp(findex) = pr(f1,f2...fM)/Zf

rem *** Find normalisation NB not analytic = log(fmax/fmin) because we are discretising f
  Zf = 0.0
  for i = 0 to FGRAIN-1
    Zf = Zf + 1.0/(i*(FMAX-FMIN)/(FGRAIN-1)+FMIN)
  next i

rem *** findex scans all possible combinations of f's
rem *** pr(f1,f2..fM) = pr(f1) * pr(f2) ...
  for findex = 0 to FGRAIN^3-1
    fp(findex) = 1.0
    for i = 0 to SECTIONS-1
      fp(findex) = fp(findex) / (Zf * ((INT(findex/FGRAIN^i) MOD FGRAIN)*(FMAX-FMIN)/(FGRAIN-1)+FMIN))
    next i
  next findex

END SUB

********************************************************************************
********************************************************************************