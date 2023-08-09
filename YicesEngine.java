package aprove.GraphUserInterface.Factories.Solvers.Engines;

import java.io.*;
import java.util.*;
import java.util.logging.*;
import java.util.regex.*;

import com.sri.yices.*;

import aprove.*;
import aprove.Framework.Logic.*;
import aprove.Framework.PropositionalLogic.*;
import aprove.Framework.PropositionalLogic.Formulae.*;
import aprove.Framework.PropositionalLogic.SMTLIB.*;
import aprove.Framework.PropositionalLogic.SMTLIB.SMTLIBFunctions.*;
import aprove.Framework.Utility.GenericStructures.*;
import aprove.Framework.Utility.SMTUtility.*;
import aprove.GraphUserInterface.Factories.Solvers.Engines.Variable;
import aprove.Strategies.Abortions.*;
import aprove.Strategies.Annotations.*;

/**
 *
 *
 * 
 */
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
 *
 *
 * 
 */
public class YicesEngine extends SMTEngine {
    private static final Logger LOG =
        Logger.getLogger("aprove.GraphUserInterface.Factories.Solvers.Engines.YicesEngine");
   

    public static class Arguments extends SMTEngine.Arguments {
        /** Extra options that are passed to yices when it is called. */
        public String ARGUMENTS = "";
        public int THEWAYTOCALL = 2;
    }

    /** The arguments given to this processor. */
    private final Arguments args;

    @ParamsViaArgumentObject
    public YicesEngine(final Arguments arguments) {
        super(arguments);
        this.args = arguments;
    }

    public YicesEngine() {
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
        Arguments arguments = new Arguments();
        final SMTFormulaToYICESVisitor vis = SMTFormulaToYICESVisitor.create();
        for (final Formula<SMTLIBTheoryAtom> f : formulas) {
            aborter.checkAbortion();
            vis.handleConstraint(f);
        }
        /*if (arguments.THEWAYTOCALL == 0) {
        final Pair<YNM, Map<String, String>> resultPair = this.solve(vis.getResult(), logic, aborter);

        resultPair.y = SMTEngine.translateResultMapToOldNames(resultPair.y, vis.getVarNameMap());

        return resultPair;
        }
        */
        if (arguments.THEWAYTOCALL == 1) {
            System.out.println("Using COM");
            final Pair<YNM, Map<String, String>> resultPair = this.solveCom(vis.getResult(), logic, aborter);

            resultPair.y = SMTEngine.translateResultMapToOldNames(resultPair.y, vis.getVarNameMap());

            System.out.print("111"+resultPair.toString());

            return resultPair;
            }
        else if (arguments.THEWAYTOCALL == 2) {
            System.out.println("Using API");
            final Pair<YNM, Map<String, String>> resultPair = this.solveAPI(vis.getResult(), logic, aborter);

            resultPair.y = SMTEngine.translateResultMapToOldNames(resultPair.y, vis.getVarNameMap());
            System.out.println("112"+vis.getResult());
            System.out.println("222"+formulas.toString());
            
            System.out.println("111"+resultPair.toString());

            return resultPair;
            }
        else {
            System.out.println("Using FILE");
            final Pair<YNM, Map<String, String>> resultPair = this.solve(vis.getResult(), logic, aborter);

            resultPair.y = SMTEngine.translateResultMapToOldNames(resultPair.y, vis.getVarNameMap());

            System.out.print("222"+formulas.toString());
            
            System.out.print("111"+resultPair.toString());

            return resultPair; 
        }
    
    }

    /**
     * {@inheritDoc}
     */
    public YNM solveAndPutIntoFormula(final List<Formula<SMTLIBTheoryAtom>> formulas,
        final SMTLogic logic,
        final Abortion aborter) throws AbortionException, WrongLogicException {
        Arguments arguments = new Arguments();
        // Call the normal solve routine:
        
        final SMTFormulaToYICESVisitor vis = SMTFormulaToYICESVisitor.create();
        for (final Formula<SMTLIBTheoryAtom> f : formulas) {
            vis.handleConstraint(f);
        }
        if (arguments.THEWAYTOCALL == 0) {
        System.out.println("Using FILE");
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
        else if (arguments.THEWAYTOCALL == 1) {
            System.out.println("Using COM");
            final Pair<YNM, Map<String, String>> resultPair = this.solveCom(vis.getResult(), logic, aborter);

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
        else if (arguments.THEWAYTOCALL == 2) {
            System.out.println("Using API");
            final Pair<YNM, Map<String, String>> resultPair = this.solveAPI(vis.getResult(), logic, aborter);

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
        else {
            final Pair<YNM, Map<String, String>> resultPair = this.solve(vis.getResult(), logic, aborter);
            System.out.println("Using FILE");

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
    }

    @Override
    public Pair<YNM, Map<String, String>> solve(final String smtString, final SMTLogic logic, final Abortion aborter)
            throws AbortionException, WrongLogicException {
        //System.err.println("Yices 2 called."); // ... it wants its model back!
        if (logic == SMTLogic.QF_NIA) {
            throw new WrongLogicException("yices 2 does not support QF_NIA");
        }
        final Process process;
        File input = null;
        try {
            aborter.checkAbortion();
            final long nanos1 = System.nanoTime();
            input = File.createTempFile("aproveSMT", ".smt2");
            input.deleteOnExit();
            final Writer inputWriter = new OutputStreamWriter(new FileOutputStream(input));
            inputWriter.write(smtString);
            inputWriter.close();
            aborter.checkAbortion();

            YicesEngine.LOG.log(Level.FINER, "SMT    to {0}\n", input.getCanonicalPath());

            YicesEngine.LOG.log(Level.FINER, "Invoking {0}\nyices2 -e");

            final Map<String, String> resMap = new LinkedHashMap<String, String>();

            aborter.checkAbortion();
            Pair<List<String>, List<String>> lines;
            try {
                final List<String> cmds = new ArrayList<>();
                cmds.add("yices-smt2");
                //cmds.add("-e");
                //This line is for yices1
                //In order to use yices2, add the mode. And change the nat to int
                
                if (this.args.ARGUMENTS != "") {
                    cmds.add(this.args.ARGUMENTS);
                }
                cmds.add(input.getCanonicalPath());
                lines = ExecHelper.exec(cmds, aborter);
                //System.out.println(smtString);
                //System.out.println(lines);
               
                
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
                YicesEngine.LOG.log(Level.FINEST, "{0}\n", line);
                //System.err.println("yices2-out: " + line);
                if (line.startsWith("unsat")) {
                    YicesEngine.LOG.log(Level.FINE, "YICES 2 says: UNSAT\n");
                    resType = YNM.NO;
                }
                if (line.startsWith("sat")) {
                    YicesEngine.LOG.log(Level.FINE, "YICES 2 says: SAT\n");
                    resType = YNM.YES;
                }
                if (line.startsWith("unknown")) {
                    YicesEngine.LOG.log(Level.FINE, "YICES 2 says: UNKNOWN\n");
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
                    //                    log.log(Level.WARNING, "Yices 2 returns an unknown line: "+line);
                }
            }
            final long nanos2 = System.nanoTime();
            if (YicesEngine.LOG.isLoggable(Level.FINE)) {
                YicesEngine.LOG.fine("SMT solving with Yices 2 took " + (nanos2 - nanos1) / 1000000L + " ms.");
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
    
    public Pair<YNM, Map<String, String>> solveCom(final String smtString, final SMTLogic logic, final Abortion aborter)
            throws AbortionException, WrongLogicException {
        //System.err.println("Yices 2 called."); // ... it wants its model back!
        if (logic == SMTLogic.QF_NIA) {
            throw new WrongLogicException("yices 2 does not support QF_NIA");
        }
        final Process process;
        File input = null;
        try {
            aborter.checkAbortion();
            final long nanos1 = System.nanoTime();
            input = File.createTempFile("aproveSMT", ".smt2");
            input.deleteOnExit();
            final Writer inputWriter = new OutputStreamWriter(new FileOutputStream(input));
            inputWriter.write(smtString);
            inputWriter.close();
            aborter.checkAbortion();

            YicesEngine.LOG.log(Level.FINER, "SMT    to {0}\n", input.getCanonicalPath());

            YicesEngine.LOG.log(Level.FINER, "Invoking {0}\nyices2 -e");

            final Map<String, String> resMap = new LinkedHashMap<String, String>();

            aborter.checkAbortion();
            Pair<List<String>, List<String>> lines;
            try {
                final List<String> cmds = new ArrayList<>();
                
                        
                if (this.args.ARGUMENTS != "") {
                    cmds.add(this.args.ARGUMENTS);
                }
              
                
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
                
                String result = test111.runYices(joined);
            
                //cmds.add(input.getCanonicalPath());
                //String commandArgs = cmds.toString();
                //Process processArgs = Runtime.getRuntime().exec(commandArgs);
                //lines = ExecHelper.exec(cmds, aborter);
                //lines = ExecYices.exec(cmds, aborter);
                List<String> stringList = new ArrayList<>();
                
                stringList.add(result);
                lines = new Pair<>(stringList,new ArrayList<>());
                System.out.print(lines);
                
                

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
                YicesEngine.LOG.log(Level.FINEST, "{0}\n", line);
                //System.err.println("yices2-out: " + line);
                if (line.startsWith("unsat")) {
                    YicesEngine.LOG.log(Level.FINE, "YICES 2 says: UNSAT\n");
                    resType = YNM.NO;
                }
                if (line.startsWith("sat")) {
                    YicesEngine.LOG.log(Level.FINE, "YICES 2 says: SAT\n");
                    resType = YNM.YES;
                }
                if (line.startsWith("unknown")) {
                    YicesEngine.LOG.log(Level.FINE, "YICES 2 says: UNKNOWN\n");
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
                    //                    log.log(Level.WARNING, "Yices 2 returns an unknown line: "+line);
                }
            }
            final long nanos2 = System.nanoTime();
            if (YicesEngine.LOG.isLoggable(Level.FINE)) {
                YicesEngine.LOG.fine("SMT solving with Yices 2 took " + (nanos2 - nanos1) / 1000000L + " ms.");
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

    public Pair<YNM, Map<String, String>> solveAPI(final String smtString, final SMTLogic logic, final Abortion aborter)
            throws AbortionException, WrongLogicException {
        //System.err.println("Yices 2 called."); // ... it wants its model back!
        if (logic == SMTLogic.QF_NIA) {
            throw new WrongLogicException("yices 2 does not support QF_NIA");
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

            YicesEngine.LOG.log(Level.FINER, "SMT    to {0}\n", input.getCanonicalPath());

            YicesEngine.LOG.log(Level.FINER, "Invoking {0}\nyices -e");

            final Map<String, String> resMap = new LinkedHashMap<String, String>();

            aborter.checkAbortion();
            Pair<List<String>, List<String>> lines = new Pair<>(new ArrayList<>(),new ArrayList<>());
            final List<String> cmds = new ArrayList<>();
            
                    
            if (this.args.ARGUMENTS != "") {
                cmds.add(this.args.ARGUMENTS);
            }
            /*
            try {
                BufferedReader reader = new BufferedReader(new FileReader(input));
                String getcommand = reader.readLine();
                while (getcommand != null) {     
                    cmds.add(getcommand);
                    //System.out.println(getcommand);
                    getcommand = reader.readLine();
                } 
                reader.close();
                
            } catch (IOException e) {
                e.printStackTrace();
            }
            String joined = String.join("\n", cmds);
            //System.out.println(joined);
           */
            try {
                
                int scalarType = Yices.newScalarType(1);
                int funcsyms = Terms.newUninterpretedTerm("funcsyms",scalarType);
                int intType = Yices.intType();
                int boolType = Yices.boolType();
                int realType = Yices.realType();
                
                String pattern1 = "\\(declare-const\\s+(\\w+)\\s+(\\w+)\\)";
                Pattern variablePattern1 = Pattern.compile(pattern1);
                Matcher matcher1 = variablePattern1.matcher(smtString);
                List<Integer> uninterpretedTerms2 = new ArrayList<>();
                List<String> testq11 = new ArrayList<>();
                List<String> testq21 = new ArrayList<>();
                while (matcher1.find()) {
                    String term = matcher1.group(1);   
                    String returntype = matcher1.group(2); 
                    VariabTerm variable1 = new VariabTerm(term, returntype);
                    testq11.add(variable1.getTerm());
                    testq21.add(variable1.getReturntype());   
                }
                for(int i = 0; i <testq11.size(); i++) {   
                    if (testq21.get(i).equals("Bool")) { 
                    //System.out.println("term:"+testq11.get(i));
                    //System.out.println("term type:"+testq21.get(i));
                    
                    int term = Terms.newUninterpretedTerm(testq11.get(i),boolType);
                    uninterpretedTerms2.add(term);
                    }
                    
                    else if (testq21.get(i).equals("funcsyms")) { 
                        //System.out.println("term:"+testq11.get(i));
                        //System.out.println("term type:"+testq21.get(i));
                        
                        int term = Terms.newUninterpretedTerm(testq11.get(i),funcsyms);
                        uninterpretedTerms2.add(term);
                    }
                    else {
                        //System.out.println("term:"+testq11.get(i));
                        //System.out.println("term type:"+testq21.get(i));
                        
                        int term = Terms.newUninterpretedTerm(testq11.get(i),intType);
                        uninterpretedTerms2.add(term);
                    }      
                } 
                
                String pattern = "\\(declare-fun\\s+(\\w+)\\s+\\(([^)]*)\\)\\s+(\\w+)\\)";
                Pattern variablePattern = Pattern.compile(pattern);
                Matcher matcher = variablePattern.matcher(smtString);
                List<Integer> uninterpretedTerms1 = new ArrayList<>();
                List<String> testq1 = new ArrayList<>();
                List<String> testq2 = new ArrayList<>();
                List<String> testq3 = new ArrayList<>();
                while (matcher.find()) {
                    String term = matcher.group(1);   
                    String returntype = matcher.group(2); 
                    String functionname = matcher.group(3);
                    Variable variable = new Variable(term, returntype, functionname);
                    System.out.println(variable.getTerm());
                    System.out.println(variable.getReturntype());
                    System.out.println(variable.getFunctionname());
                    testq1.add(variable.getTerm());
                    testq2.add(variable.getReturntype());
                    testq3.add(variable.getFunctionname());
                }
           
                for(int i = 0; i <testq1.size(); i++) {     
                    //System.out.println(testq2.get(i));
                    
                    if (testq2.get(i).equals("Bool")) { 
                        int getType1 = boolType;
                        int term = Terms.newUninterpretedFunction(testq1.get(i),getType1,intType);            
                        //System.out.println("func:"+testq1.get(i));
               
                        uninterpretedTerms1.add(term);
                        }
                    else if (testq2.get(i).equals("Real")) { 
                        int getType1 = realType;
                        int term = Terms.newUninterpretedFunction(testq1.get(i),getType1,intType);
                        //System.out.println("func:"+testq1.get(i));
                    
                        uninterpretedTerms1.add(term);
                        }
                    else if (testq2.get(i).equals("Int Int")) { 
                        int term = Terms.newUninterpretedFunction(testq1.get(i),intType,intType,boolType);
                        //System.out.println("func:"+testq1.get(i));
                    
                        uninterpretedTerms1.add(term);
                       }
                    
                    else if (testq2.get(i).equals("funcsyms")) { 
                        int term = Terms.newUninterpretedFunction(testq1.get(i),funcsyms,intType);
                        //System.out.println("func:"+testq1.get(i));
                    
                        uninterpretedTerms1.add(term);
                        }
                        
                    else { 
                        int getType1 = intType;
                        int term = Terms.newUninterpretedFunction(testq1.get(i),getType1,intType);
                        //System.out.println("func:"+testq1.get(i));
                
                        uninterpretedTerms1.add(term);
                        }
                }
                String withoutcheck = TestForAPI.removeLastLine(smtString);
                System.out.print(smtString);
                System.out.print("without check done\n");
                String pwithoutset = TestForAPI.withoutSet(withoutcheck);
                //System.out.print(pwithoutset);
                System.out.print("without Set option done\n");
                String pwithoutsort = TestForAPI.withoutSort(pwithoutset);
                //System.out.print(pwithoutsort);
                System.out.print("without declare-sort done\n");
                String pwithoutdeclare = TestForAPI.withoutdeclare(pwithoutsort);
                //System.out.print(pwithoutdeclare);
                System.out.print("without declare-fun and -const done\n");
                String pwithoutassert = TestForAPI.withoutAssert(pwithoutdeclare);
                System.out.print(pwithoutassert);
                System.out.print("without assert done\n");
                String result = TestForAPI.toGetResult(pwithoutassert);
                System.out.print(result);  
                List<String> stringList = new ArrayList<>();
   /*
                int scalarType = Yices.newScalarType(1);
                int funcsyms = Terms.newUninterpretedTerm("funcsyms",scalarType);
                int intType = Yices.intType();
                int boolType = Yices.boolType();
                int realType = Yices.realType();
                
                String pattern = "\\(define\\s+(\\w+)::\\(->\\s+(\\w+)\\s+(\\w+)\\)\\)";
                Pattern variablePattern = Pattern.compile(pattern);
                Matcher matcher = variablePattern.matcher(smtString);
                List<Integer> uninterpretedTerms1 = new ArrayList<>();
                List<String> testq1 = new ArrayList<>();
                List<String> testq2 = new ArrayList<>();
                List<String> testq3 = new ArrayList<>();
                while (matcher.find()) {
                    String term = matcher.group(1);   
                    String returntype = matcher.group(2); 
                    String functionname = matcher.group(3);
                    Variable variable = new Variable(term, returntype, functionname);
                    //System.out.println(variable.getTerm());
                    //System.out.println(variable.getReturntype());
                    //System.out.println(variable.getFunctionname());
                    testq1.add(variable.getTerm());
                    testq2.add(variable.getReturntype());
                    testq3.add(variable.getFunctionname());
                }

            
                for(int i = 0; i <testq1.size(); i++) {     
                    
                    if (testq2.get(i).equals("bool")) { 
                        int getType1 = boolType;
                        int term = Terms.newUninterpretedFunction(testq1.get(i),intType,getType1);            
                        System.out.println("func with 2:"+testq1.get(i));
               
                        uninterpretedTerms1.add(term);
                        }
                    else if (testq2.get(i).equals("real")) { 
                        int getType1 = realType;
                        int term = Terms.newUninterpretedFunction(testq1.get(i),intType,getType1);
                        System.out.println("func with 2:"+testq1.get(i));
                    
                        uninterpretedTerms1.add(term);
                        }
                    else { 
                        int getType1 = intType;
                        int term = Terms.newUninterpretedFunction(testq1.get(i),getType1,intType);
                        System.out.println("func with 2:"+testq1.get(i));
                
                        uninterpretedTerms1.add(term);
                        }
                }

                String pattern1 = "\\(define\\s+(\\w+)::(\\w+)\\)";
                Pattern variablePattern1 = Pattern.compile(pattern1);
                Matcher matcher1 = variablePattern1.matcher(smtString);
                List<Integer> uninterpretedTerms2 = new ArrayList<>();
                List<String> testq11 = new ArrayList<>();
                List<String> testq21 = new ArrayList<>();
                while (matcher1.find()) {
                    String term = matcher1.group(1);   
                    String returntype = matcher1.group(2); 
                    VariabTerm variable1 = new VariabTerm(term, returntype);
                    testq11.add(variable1.getTerm());
                    testq21.add(variable1.getReturntype());   
                }
                for(int i = 0; i <testq11.size(); i++) {     
                    
                    int term = Terms.newUninterpretedTerm(testq11.get(i),intType);
                    uninterpretedTerms2.add(term);
                } 
                
                String pattern2 = "\\(define\\s+(\\w+)::\\(->\\s+(\\w+)\\s+(\\w+)\\s+(\\w+)\\)\\)";
                Pattern variablePattern2 = Pattern.compile(pattern2);
                Matcher matcher2 = variablePattern2.matcher(smtString);
                List<Integer> uninterpretedTerms3 = new ArrayList<>();
                List<String> testq41 = new ArrayList<>();
                List<String> testq42 = new ArrayList<>();
                List<String> testq43 = new ArrayList<>();
                List<String> testq44 = new ArrayList<>();       
                while (matcher2.find()) {
                    String term2 = matcher2.group(1);   
                    String g2 = matcher2.group(2); 
                    String g3 = matcher2.group(3); 
                    String g4 = matcher2.group(4); 
                    VarFour variable3 = new VarFour(term2, g2, g3, g4);
                    testq41.add(variable3.getTerm());
                    testq42.add(variable3.getReturntype());   
                    testq43.add(variable3.getFunctionname1());
                    testq44.add(variable3.getFunctionname2());          
                }
            
                for(int j = 0; j <testq41.size(); j++) {     
                   
                    int term3 = Terms.newUninterpretedFunction(testq41.get(j),intType,intType, boolType);
                    uninterpretedTerms3.add(term3);
                }  
                
                String pattern3 = "\\(define-type\\s+(\\w+)\\s+\\(scalar\\s+(\\w+)\\s+\\)\\)";
                Pattern variablePattern3 = Pattern.compile(pattern3);
                Matcher matcher3 = variablePattern3.matcher(smtString);

                String withoutcheck = TestForYicesAPIold.removeLastLine(smtString);
                //System.out.print(withoutcheck);
         
                String pp = TestForAPI.withoutAssert(withoutcheck);
                
                
                String withoutDineType = TestForYicesAPIold.withoutDefinetype(pp);
           //     System.out.print(withoutDineType);
            //    System.out.print("without define type done\n");
                
                String filteredProblem = TestForYicesAPIold.withoutDefine(pp);
                //System.out.print(filteredProblem);
                //System.out.print("without define done\n");
                
                String result = TestForYicesAPIold.toGetResult(filteredProblem);
                
              
                System.out.println(result);
                //String withoutcheck = TestForAPI.removeLastLine(joined);
                //String pp = TestForAPI.withoutAssert(withoutcheck);   
                //String filteredProblem = TestForAPI.withoutDefine(pp);
                //String result = TestForAPI.toGetResult(filteredProblem);   
      */          
               
                stringList.add(result);
                lines = new Pair<>(stringList,new ArrayList<>()); 
                System.out.println(lines);
                
            } catch(Exception e){
                System.err.println(e);
            }

            for (final String line : lines.y) {
                if ("Error: feature not supported: non linear problem.".equals(line)) {
                    throw new WrongLogicException(line);
                } else {
                    System.err.println("YICES stderr: " + line);
                }
            }
            YNM resType = YNM.MAYBE;
            aborter.checkAbortion();
            final Iterator<String> it = lines.x.iterator();
            while (it.hasNext()) {
                final String line = it.next();
                YicesEngine.LOG.log(Level.FINEST, "{0}\n", line);
                //System.err.println("yices2-out: " + line);
                if (line.startsWith("unsat")) {
                    YicesEngine.LOG.log(Level.FINE, "YICES 2 says: UNSAT\n");
                    resType = YNM.NO;
                }
                if (line.startsWith("sat")) {
                    YicesEngine.LOG.log(Level.FINE, "YICES 2 says: SAT\n");
                    resType = YNM.YES;
                }
                if (line.startsWith("unknown")) {
                    YicesEngine.LOG.log(Level.FINE, "YICES 2 says: UNKNOWN\n");
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
                    //                    log.log(Level.WARNING, "Yices 2 returns an unknown line: "+line);
                }
            }
            final long nanos2 = System.nanoTime();
            if (YicesEngine.LOG.isLoggable(Level.FINE)) {
                YicesEngine.LOG.fine("SMT solving with Yices 2 took " + (nanos2 - nanos1) / 1000000L + " ms.");
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