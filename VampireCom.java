package aprove.GraphUserInterface.Factories.Solvers.Engines;


import java.io.*;
import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.Framework.Logic.*;
import aprove.Framework.PropositionalLogic.*;
import aprove.Framework.PropositionalLogic.Formulae.*;
import aprove.Framework.PropositionalLogic.SMTLIB.*;
import aprove.Framework.PropositionalLogic.SMTLIB.SMTLIBFunctions.*;
import aprove.Framework.Utility.GenericStructures.*;
import aprove.Framework.Utility.SMTUtility.*;
import aprove.Strategies.Abortions.*;
import aprove.Strategies.Annotations.*;

/**
 * Calls cvc5 using commandline
 *
 * 
 */
public class VampireCom extends SMTEngine {
    private static final Logger LOG =
        Logger.getLogger("aprove.GraphUserInterface.Factories.Solvers.Engines.YicesEngine");

    public static class Arguments extends SMTEngine.Arguments {
        /** Extra options that are passed to yices when it is called. */
        public String ARGUMENTS = "";
    }

    /** The arguments given to this processor. */
    private final Arguments args;

    @ParamsViaArgumentObject
    public VampireCom(final Arguments arguments) {
        super(arguments);
        this.args = arguments;
    }

    public VampireCom() {
        this(new Arguments());
    }

    /** {@inheritDoc} */
    @Override
    public YNM satisfiable(final List<Formula<SMTLIBTheoryAtom>> formulas, final SMTLogic logic, final Abortion aborter)
            throws AbortionException, WrongLogicException {
        return this.solveAndPutIntoFormula(formulas, logic, aborter);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Pair<YNM, Map<String, String>> solve(final List<Formula<SMTLIBTheoryAtom>> formulas,
        final SMTLogic logic,
        final Abortion aborter) throws AbortionException, WrongLogicException {
        final SMTFormulaToYICESVisitor vis = SMTFormulaToYICESVisitor.create();
        for (final Formula<SMTLIBTheoryAtom> f : formulas) {
            aborter.checkAbortion();
            vis.handleConstraint(f);
        }
        final Pair<YNM, Map<String, String>> resultPair = this.solve(vis.getResult(), logic, aborter);

        resultPair.y = SMTEngine.translateResultMapToOldNames(resultPair.y, vis.getVarNameMap());

        return resultPair;
    }

    /**
     * {@inheritDoc}
     */
    public YNM solveAndPutIntoFormula(final List<Formula<SMTLIBTheoryAtom>> formulas,
        final SMTLogic logic,
        final Abortion aborter) throws AbortionException, WrongLogicException {
        // Call the normal solve routine:
        final SMTFormulaToYICESVisitor vis = SMTFormulaToYICESVisitor.create();
        for (final Formula<SMTLIBTheoryAtom> f : formulas) {
            vis.handleConstraint(f);
        }
        final Pair<YNM, Map<String, String>> resultPair = this.solve(vis.getResult(), logic, aborter);

        //Be defensive:
        if (resultPair == null) {
            return YNM.MAYBE;
        }

        final YNM resType = resultPair.x;
        final Map<String, String> result = resultPair.y;
        if (result == null) {
            assert (resType != YNM.YES) : "SMT returned SAT, but we have no model!";
            return resType;
        }

        final SMTLIBVarNameMap varNameMap = vis.getVarNameMap();
        final Map<String, SMTLIBAssignableSemantics> nameToVarMap = varNameMap.getNameToVarMap();
        for (final Map.Entry<String, String> e : result.entrySet()) {
            final String key = e.getKey();
            final String val = e.getValue();

            if (key.startsWith("(")) {
                // Function value
                final SMTLIBFunction<?> v = (SMTLIBFunction<?>) nameToVarMap.get(key);
                if (v != null) {
                    final String[] sArr = key.split(" ");
                    final List<String> params = new ArrayList<String>(sArr.length);
                    for (final String element : sArr) {
                        params.add(element);
                    }
                    v.setResult(params, val);
                }
            } else {
                // Variable value
                final SMTLIBVariable<?> v = (SMTLIBVariable<?>) nameToVarMap.get(key);
                if (v != null) {
                    v.setResult(val);
                }
            }
        }
        return resType;
    }

    @Override
    public Pair<YNM, Map<String, String>> solve(final String smtString, final SMTLogic logic, final Abortion aborter)
            throws AbortionException, WrongLogicException {
        //System.err.println("Yices called."); // ... it wants its model back!
        if (logic == SMTLogic.QF_NIA) {
            throw new WrongLogicException("yices does not support QF_NIA");
        }
        final Process process;
        File input = null;
        try {
            aborter.checkAbortion();
            final long nanos1 = System.nanoTime();
            //use it for file input
            input = File.createTempFile("aproveSMT", ".smt2");
            input.deleteOnExit();
            //System.out.print(input);
            
            final Writer inputWriter = new OutputStreamWriter(new FileOutputStream(input));
            inputWriter.write(smtString);
            inputWriter.close();
            aborter.checkAbortion();

            VampireCom.LOG.log(Level.FINER, "SMT    to {0}\n", input.getCanonicalPath());

            VampireCom.LOG.log(Level.FINER, "Invoking {0}\nyices -e");

            final Map<String, String> resMap = new LinkedHashMap<String, String>();

            aborter.checkAbortion();
            Pair<List<String>, List<String>> lines = new Pair<>(new ArrayList<>(),new ArrayList<>());
            try {
                final List<String> cmds = new ArrayList<>();
                //cmds.add("yices");
                //cmds.add("--mode=one-shot");
                        
                if (this.args.ARGUMENTS != "") {
                    cmds.add(this.args.ARGUMENTS);
                }
                //final List<String> cmdsnew = new ArrayList<>();
                
                
                try {
                    BufferedReader reader = new BufferedReader(new FileReader(input));
                    String getcommand = reader.readLine();
                    while (getcommand != null) {     
                        cmds.add(getcommand);
                        //System.out.println(getcommand);
                        getcommand = reader.readLine();
                    } 
                    reader.close();
                    
                    //String result = test111.runYices(getcommand);
                    //System.out.print(result);
                } catch (IOException e) {
                    e.printStackTrace();
                }
                
                
                //cmds.add("(exit)");
                String joined = String.join("\n", cmds);
                
                String result = RunVampire.runVampire(joined);
                //cmds.add(input.getCanonicalPath());
                //String commandArgs = cmds.toString();
                //Process processArgs = Runtime.getRuntime().exec(commandArgs);
                //lines = ExecHelper.exec(cmds, aborter);
                //lines = ExecYices.exec(cmds, aborter);
                List<String> stringList = new ArrayList<>();
                
                stringList.add(result);
                lines = new Pair<>(stringList,new ArrayList<>());
                //System.out.print(lines);
                
                

                //System.out.print(cmds);
                //System.out.print(joined);
            } catch (final InterruptedException e) {
                assert false : "SMT interrupted!";
                return new Pair<YNM, Map<String, String>>(YNM.MAYBE, resMap);
            }

            for (final String line : lines.y) {
                if ("Error: feature not supported: non linear problem.".equals(line)) {
                    throw new WrongLogicException(line);
                } else {
                    System.err.println("YICES stderr: " + line);
                }
            }
            YNM resType = YNM.MAYBE;
            // aborter.checkAbortion();
            final Iterator<String> it = lines.x.iterator();
            while (it.hasNext()) {
                final String line = it.next();
                VampireCom.LOG.log(Level.FINEST, "{0}\n", line);
                //System.err.println("yices-out: " + line);
                if (line.startsWith("unsat")) {
                    VampireCom.LOG.log(Level.FINE, "YICES says: UNSAT\n");
                    resType = YNM.NO;
                }
                if (line.startsWith("sat")) {
                    VampireCom.LOG.log(Level.FINE, "YICES says: SAT\n");
                    resType = YNM.YES;
                }
                if (line.startsWith("unknown")) {
                    VampireCom.LOG.log(Level.FINE, "YICES says: UNKNOWN\n");
                    resType = YNM.MAYBE;
                }
                if (line.startsWith("(")) {
                    if (line.length() < 4) {
                        // A line with no information - very strange!
                        continue;
                    }
                    if (line.charAt(3) == '(') {
                        // Function result
                        String[] sArr = line.split(" ");
                        if (sArr.length < 4) {
                            // maybe the line is too long and the result is continued in the next line?
                            if (it.hasNext()) {
                                String nextLine = it.next();
                                nextLine = nextLine.trim();
                                sArr = (line + " " + nextLine).split(" ");
                            }
                        }

                        assert (sArr.length >= 4) : line + " " + input.getCanonicalPath();
                        final StringBuilder resx = new StringBuilder();
                        resx.append(sArr[1]);
                        for (int i = 2; i < sArr.length - 1; i++) {
                            resx.append(" ");
                            resx.append(sArr[i]);
                        }
                        final String resy = sArr[sArr.length - 1].substring(0, sArr[sArr.length - 1].length() - 1);
                        resMap.put(resx.toString(), resy);
                    } else {
                        // Variable result
                        final String[] sArr = line.split(" ");
                        if (sArr.length != 3) {
                            if (!Globals.DEBUG_NONE) {
                                System.err.println("line: ");
                                System.err.println(line);
                                System.err.println("following three lines: ");
                                int count = 0;
                                while (it.hasNext() && count < 3) {
                                    count++;
                                    final String nextLine = it.next();
                                    System.err.println(nextLine);
                                }
                            }
                            assert (false);
                        }
                        final String res = sArr[2].substring(0, sArr[2].length() - 1);
                        resMap.put(sArr[1], res);
                    }
                    //                } else {
                    //                    log.log(Level.WARNING, "Yices returns an unknown line: "+line);
                }
            }
            final long nanos2 = System.nanoTime();
            if (VampireCom.LOG.isLoggable(Level.FINE)) {
                VampireCom.LOG.fine("SMT solving with Yices took " + (nanos2 - nanos1) / 1000000L + " ms.");
            }
            input.delete();
            aborter.checkAbortion();
            return new Pair<YNM, Map<String, String>>(resType, resMap);

        } catch (final NoSuchElementException e) {
            // just return null
        } catch (final IOException e) {
            e.printStackTrace();
        } finally {
            if (input != null) {
                input.delete();
            }
        }
        return null;
    }
}