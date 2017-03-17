package edu.ucla.cs.mine;

import static org.junit.Assert.*;

import java.util.ArrayList;
import java.util.HashSet;

import org.junit.Test;

public class PredicateMinerTest {
	@Test
	public void testConditionOne() {
		HashSet<String> vars = new HashSet<String>();
		vars.add("a");
		assertEquals("a && true", PredicatePatternMiner.condition(vars, "a && b"));
	}

	@Test
	public void testConditionAll() {
		new LightweightPredicateMiner(
				new ArrayList<String>());
		HashSet<String> vars = new HashSet<String>();
		vars.add("a");
		vars.add("b");
		assertEquals("a && b", PredicatePatternMiner.condition(vars, "a && b"));
	}

	@Test
	public void testConditionNone() {
		new LightweightPredicateMiner(
				new ArrayList<String>());
		HashSet<String> vars = new HashSet<String>();
		vars.add("c");
		assertEquals("true", PredicatePatternMiner.condition(vars, "a && b"));
	}

	@Test
	public void testConditionNestedPredicate1() {
		HashSet<String> vars = new HashSet<String>();
		vars.add("c");
		assertEquals("(true) && c", PredicatePatternMiner.condition(vars, "(a || b) && c"));
	}

	@Test
	public void testConditionNestedPredicate2() {
		HashSet<String> vars = new HashSet<String>();
		vars.add("c");
		assertEquals("(true || c) && true",
				PredicatePatternMiner.condition(vars, "((a + b > 0) || c) && d"));
		vars.add("a");
		assertEquals("((a + b > 0) || c) && true",
				PredicatePatternMiner.condition(vars, "((a + b > 0) || c) && d"));
	}

	@Test
	public void testConditionPredicateWithNegation() {
		HashSet<String> vars = new HashSet<String>();
		vars.add("c");
		assertEquals("(true || c) && true",
				PredicatePatternMiner.condition(vars, "((a + b > 0) || c) && !d"));
	}

	@Test
	public void conditionPredicateDoubleNegation() {
		HashSet<String> vars = new HashSet<String>();
		vars.add("file");
		assertEquals("!file.exists && true",
				PredicatePatternMiner.condition(vars, "!file.exists && !(!destDir.exists)"));
	}

	@Test
	public void testConditionPredicateNegationOfTwoTrue() {
		HashSet<String> vars = new HashSet<String>();
		vars.add("file");
		assertEquals(
				"!file.exists && true",
				PredicatePatternMiner.condition(vars,
						"!file.exists && !(a && b) && !(b || c) && !(a&&b&&c) && !(a||b&&c)"));
	}

	@Test
	public void conditionPredicateWithArguments() {
		HashSet<String> vars = new HashSet<String>();
		vars.add("file");
		assertEquals("!file.exists() && true",
				PredicatePatternMiner.condition(vars, "!file.exists() && !(!destDir.exists())"));
	}

	@Test
	public void testNormalizePost17149392() {
		String predicate = "files != null && files.length > 0";
		ArrayList<String> rcv_candidates = new ArrayList<String>();
		rcv_candidates.add("f");
		ArrayList<ArrayList<String>> args_candidates = new ArrayList<ArrayList<String>>();
		String norm = PredicatePatternMiner.normalize(predicate,
				rcv_candidates, args_candidates);
		assertEquals(predicate, norm);
	}

	@Test
	public void testConditionPost17149392() {
		HashSet<String> vars = new HashSet<String>();
		vars.add("f");
		assertEquals("true",
				PredicatePatternMiner.condition(vars, "files != null && files.length > 0"));
	}

	@Test
	public void testNormalizeNameInTheMiddle() {
		String predicate = "it.hasNext() && entity==null";
		ArrayList<String> rcv_candidates = new ArrayList<String>();
		rcv_candidates.add("it");
		ArrayList<ArrayList<String>> args_candidates = new ArrayList<ArrayList<String>>();
		String norm = PredicatePatternMiner.normalize(predicate,
				rcv_candidates, args_candidates);
		String expected = "rcv.hasNext() && entity==null";
		assertEquals(expected, norm);
	}

	@Test
	public void testContainsVar() {
		String var1 = "f";
		String var2 = "file";
		String var3 = "files";
		String clause = "files!=null";

		assertFalse(PredicatePatternMiner.containsVar(var1, clause));
		assertFalse(PredicatePatternMiner.containsVar(var2, clause));
		assertTrue(PredicatePatternMiner.containsVar(var3, clause));
	}

	@Test
	public void testReplaceVar() {
		String var1 = "f";
		String var2 = "file";
		String var3 = "files";
		String clause = "files!=null";

		assertEquals("files!=null",
				PredicatePatternMiner.replaceVar(var1, clause, "rcv"));
		assertEquals("files!=null",
				PredicatePatternMiner.replaceVar(var2, clause, "rcv"));
		assertEquals("rcv!=null",
				PredicatePatternMiner.replaceVar(var3, clause, "rcv"));
	}

	@Test
	public void testExtractReceiverWithTypeCasting() {
		String path = "/home/troy/research/BOA/Maple/example/Iterator.next/small-sequence.txt";
		String sequence_path = "/home/troy/research/BOA/Maple/example/Iterator.next/small-output.txt";
		TraditionalPredicateMiner pm = new TraditionalPredicateMiner(
				new ArrayList<String>(), path, sequence_path);
		String expr = "e=(Map.Entry) i.next()";
		String apiName = "next";
		assertEquals("i", pm.getReceiver(expr, apiName));
	}

	@Test
	public void testConditionVarNameInTheMiddle() {
		HashSet<String> vars = new HashSet<String>();
		vars.add("t_jspFile");
		String predicate = "!flag && !(!jspFile.exists()||jspFile.isDirectory()) && !(cache!=null) && flag && !(a||b||c||d) && converter.containJspTag() && !(!context) && pagecontext.getPageType().equals(CMSLink.TYPE_STATIC_PAGE+\"\",)";
		assertEquals("true", PredicatePatternMiner.condition(vars, predicate));
	}
	
	@Test
	public void testConditionConflictingNames() {
		// this case should never happen
		HashSet<String> vars = new HashSet<String>();
		vars.add("deployedMarker");
		String predicate = "files && isDeploymentFromODEFileSystemAllowed()&&files!=null";
		assertEquals("true!=null", PredicatePatternMiner.condition(vars, predicate));
	}
	
	@Test
	public void testConditionStringContainExclaimation() {
		HashSet<String> vars = new HashSet<String>();
		vars.add("f");
		String predicate = "!(execln.contentEquals(\"!Load\",))";
		assertEquals("true", PredicatePatternMiner.condition(vars, predicate));
	}
}
