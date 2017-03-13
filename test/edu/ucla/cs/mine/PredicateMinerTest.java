package edu.ucla.cs.mine;

import static org.junit.Assert.*;

import java.util.ArrayList;
import java.util.HashSet;

import org.junit.Ignore;
import org.junit.Test;

import edu.ucla.cs.model.PredicateCluster;
import edu.ucla.cs.utils.SAT;

public class PredicateMinerTest {
	@Test
	public void testConditionOne() {
		LightweightPredicateMiner pm = new LightweightPredicateMiner(
				new ArrayList<String>());
		HashSet<String> vars = new HashSet<String>();
		vars.add("a");
		assertEquals("a && true", 
				pm.condition(vars, "a && b"));
	}

	@Test
	public void testConditionAll() {
		LightweightPredicateMiner pm = new LightweightPredicateMiner(
				new ArrayList<String>());
		HashSet<String> vars = new HashSet<String>();
		vars.add("a");
		vars.add("b");
		assertEquals("a && b", 
				pm.condition(vars, "a && b"));
	}

	@Test
	public void testConditionNone() {
		LightweightPredicateMiner pm = new LightweightPredicateMiner(
				new ArrayList<String>());
		HashSet<String> vars = new HashSet<String>();
		vars.add("c");
		assertEquals("true && true",
				pm.condition(vars, "a && b"));
	}

	@Test
	public void testConditionNestedPredicate1() {
		LightweightPredicateMiner pm = new LightweightPredicateMiner(
				new ArrayList<String>());
		HashSet<String> vars = new HashSet<String>();
		vars.add("c");
		assertEquals("(true || true) && c",
				pm.condition(vars, "(a || b) && c"));
	}

	@Test
	public void testConditionNestedPredicate2() {
		LightweightPredicateMiner pm = new LightweightPredicateMiner(
				new ArrayList<String>());
		HashSet<String> vars = new HashSet<String>();
		vars.add("c");
		assertEquals("(true || c) && true", 
				pm.condition(vars, "((a + b > 0) || c) && d"));
		vars.add("a");
		assertEquals("((a + b > 0) || c) && true",
				pm.condition(vars, "((a + b > 0) || c) && d"));
	}

	@Test
	public void testConditionPredicateWithNegation() {
		LightweightPredicateMiner pm = new LightweightPredicateMiner(
				new ArrayList<String>());
		HashSet<String> vars = new HashSet<String>();
		vars.add("c");
		assertEquals("(true || c) && true",
				pm.condition(vars, "((a + b > 0) || c) && !d"));
	}
	
	@Test
	public void conditionPredicateDoubleNegation() {
		LightweightPredicateMiner pm = new LightweightPredicateMiner(
				new ArrayList<String>());
		HashSet<String> vars = new HashSet<String>();
		vars.add("file");
		assertEquals("!file.exists && true",
				pm.condition(vars, "!file.exists && !(!destDir.exists)"));
	}

	@Test
	public void conditionPredicateWithArguments() {
		LightweightPredicateMiner pm = new LightweightPredicateMiner(
				new ArrayList<String>());
		HashSet<String> vars = new HashSet<String>();
		vars.add("file");
		assertEquals("!file.exists() && true",
				pm.condition(vars, "!file.exists() && !(!destDir.exists())"));
	}

	@Test
	public void testNormalizePost17149392() {
		String predicate = "files != null && files.length > 0";
		ArrayList<String> rcv_candidates = new ArrayList<String>();
		rcv_candidates.add("f");
		ArrayList<ArrayList<String>> args_candidates = new ArrayList<ArrayList<String>>();
		String norm = PredicatePatternMiner.normalize(predicate, rcv_candidates, args_candidates);
		assertEquals(predicate, norm);
	}
	
	@Test
	public void testConditionPost17149392() {
		LightweightPredicateMiner pm = new LightweightPredicateMiner(
				new ArrayList<String>());
		HashSet<String> vars = new HashSet<String>();
		vars.add("f");
		assertEquals("true && true",
				pm.condition(vars, "files != null && files.length > 0"));
	}
	
	@Test
	public void testNormalizeNameInTheMiddle() {
		String predicate = "it.hasNext() && entity==null";
		ArrayList<String> rcv_candidates = new ArrayList<String>();
		rcv_candidates.add("it");
		ArrayList<ArrayList<String>> args_candidates = new ArrayList<ArrayList<String>>();
		String norm = PredicatePatternMiner.normalize(predicate, rcv_candidates, args_candidates);
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
		
		assertEquals("files!=null", PredicatePatternMiner.replaceVar(var1, clause, "rcv"));
		assertEquals("files!=null", PredicatePatternMiner.replaceVar(var2, clause, "rcv"));
		assertEquals("rcv!=null", PredicatePatternMiner.replaceVar(var3, clause, "rcv"));
	}
	
	@Test
	public void testExtractReceiverWithTypeCasting() {
		TraditionalPredicateMiner pm = new TraditionalPredicateMiner(
				new ArrayList<String>());
		String expr = "e=(Map.Entry) i.next()";
		String apiName = "next";
		assertEquals("i",
				pm.getReceiver(expr, apiName));
	}
}
