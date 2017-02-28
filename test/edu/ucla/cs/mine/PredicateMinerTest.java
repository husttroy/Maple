package edu.ucla.cs.mine;

import static org.junit.Assert.*;

import java.util.ArrayList;
import java.util.HashSet;

import org.junit.Ignore;
import org.junit.Test;

import edu.ucla.cs.model.PredicateCluster;

public class PredicateMinerTest {
	@Test
	public void testConditionOne() {
		LightweihgtPredicateMiner pm = new LightweihgtPredicateMiner(
				new ArrayList<String>());
		HashSet<String> vars = new HashSet<String>();
		vars.add("a");
		assertEquals("a && true", 
				pm.condition(vars, "a && b"));
	}

	@Test
	public void testConditionAll() {
		LightweihgtPredicateMiner pm = new LightweihgtPredicateMiner(
				new ArrayList<String>());
		HashSet<String> vars = new HashSet<String>();
		vars.add("a");
		vars.add("b");
		assertEquals("a && b", 
				pm.condition(vars, "a && b"));
	}

	@Test
	public void testConditionNone() {
		LightweihgtPredicateMiner pm = new LightweihgtPredicateMiner(
				new ArrayList<String>());
		HashSet<String> vars = new HashSet<String>();
		vars.add("c");
		assertEquals("true && true",
				pm.condition(vars, "a && b"));
	}

	@Test
	public void testConditionNestedPredicate1() {
		LightweihgtPredicateMiner pm = new LightweihgtPredicateMiner(
				new ArrayList<String>());
		HashSet<String> vars = new HashSet<String>();
		vars.add("c");
		assertEquals("(true || true) && c",
				pm.condition(vars, "(a || b) && c"));
	}

	@Test
	public void testConditionNestedPredicate2() {
		LightweihgtPredicateMiner pm = new LightweihgtPredicateMiner(
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
		LightweihgtPredicateMiner pm = new LightweihgtPredicateMiner(
				new ArrayList<String>());
		HashSet<String> vars = new HashSet<String>();
		vars.add("c");
		assertEquals("(true || c) && true",
				pm.condition(vars, "((a + b > 0) || c) && !d"));
	}
	
	@Test
	public void conditionPredicateDoubleNegation() {
		LightweihgtPredicateMiner pm = new LightweihgtPredicateMiner(
				new ArrayList<String>());
		HashSet<String> vars = new HashSet<String>();
		vars.add("file");
		assertEquals("!file.exists && true",
				pm.condition(vars, "!file.exists && !(!destDir.exists)"));
	}

	@Test
	public void conditionPredicateWithArguments() {
		LightweihgtPredicateMiner pm = new LightweihgtPredicateMiner(
				new ArrayList<String>());
		HashSet<String> vars = new HashSet<String>();
		vars.add("file");
		assertEquals("!file.exists() && true",
				pm.condition(vars, "!file.exists() && !(!destDir.exists())"));
	}

	@Test
	public void testSymbolizeBasic() {
		LightweihgtPredicateMiner pm = new LightweihgtPredicateMiner(
				new ArrayList<String>());
		String rel = pm.symbolize("!rcv.exists");
		assertEquals("!b0", rel);
	}
	
	@Test
	public void testSymbolizeBasicWithArg() {
		LightweihgtPredicateMiner pm = new LightweihgtPredicateMiner(
				new ArrayList<String>());
		String rel = pm.symbolize("!rcv.exists(c)");
		assertEquals("!b0", rel);
	}
	
	@Test
	public void testSymbolizeDoubleNegation() {
		LightweihgtPredicateMiner pm = new LightweihgtPredicateMiner(
				new ArrayList<String>());
		String rel = pm.symbolize("!(!rcv.exists) && !rcv.exists");
		assertEquals("!(!b0) && !b0", rel);
	}

	@Test
	public void testSymbolizeWithUncessaryParentheses() {
		LightweihgtPredicateMiner pm = new LightweihgtPredicateMiner(
				new ArrayList<String>());
		String rel = pm.symbolize("!(rcv.exists)");
		assertEquals("!b0", rel);
	}

	@Test
	public void testSymbolizeWithUnbalancedParentheses() {
		LightweihgtPredicateMiner pm = new LightweihgtPredicateMiner(
				new ArrayList<String>());
		String rel = pm
				.symbolize("((s.length + 1 > 0) || flag) && Environment.SSS");
		assertEquals("((i0 + 1 > 0) || b0) && b1", rel);
	}

	@Test
	public void testSymbolizeWithLiterals() {
		LightweihgtPredicateMiner pm = new LightweihgtPredicateMiner(
				new ArrayList<String>());
		String rel = pm.symbolize("((s.length + 1 > 0) || (true)) && false");
		assertEquals("((i0 + 1 > 0) || true) && false", rel);
	}

	@Test
	public void testZ3QueryGeneration() {
		LightweihgtPredicateMiner pm = new LightweihgtPredicateMiner(
				new ArrayList<String>());
		String p1 = "(! (== 1 a0))";
		String p2 = "(&& b0 b2)";
		String query = "(assert (or (and (not (= 1 a0)) (not (and b0 b2))) (and (not (not (= 1 a0))) (and b0 b2))))\n(check-sat)";
		assertEquals(query, pm.generateZ3Query(p1, p2));
	}

	@Test
	public void testZ3Runner() {
		LightweihgtPredicateMiner pm = new LightweihgtPredicateMiner(
				new ArrayList<String>());
		String query = "(declare-const a0 Int)\n(declare-const b0 Bool)\n(declare-const b2 Bool)(assert (and (not (= 1 a0)) (not (and b0 b2))))\n(check-sat)";
		assertTrue(pm.isSAT(query));
	}

	@Test
	public void testEquivalenceChecker() {
		LightweihgtPredicateMiner pm = new LightweihgtPredicateMiner(
				new ArrayList<String>());
		PredicateCluster pc1 = new PredicateCluster(
				"true && arg0 >= 1 && !(rcv.exists)", 1);
		PredicateCluster pc2 = new PredicateCluster("1 <= arg0 && !rcv.exists",
				1);
		assertTrue(pm.checkEquivalence(pc1, pc2));
	}

	@Test
	public void testEquivalenceWithFalse() {
		LightweihgtPredicateMiner pm = new LightweihgtPredicateMiner(
				new ArrayList<String>());
		PredicateCluster pc1 = new PredicateCluster("false", 1);
		PredicateCluster pc2 = new PredicateCluster("1 <= arg0 && !rcv.exists",
				1);
		assertFalse(pm.checkEquivalence(pc1, pc2));
	}

	@Test
	public void testEquivalenceWithTrue() {
		LightweihgtPredicateMiner pm = new LightweihgtPredicateMiner(
				new ArrayList<String>());
		PredicateCluster pc1 = new PredicateCluster(
				"true && arg0 >= 1 && !(rcv.exists)", 1);
		PredicateCluster pc2 = new PredicateCluster("true", 1);
		assertFalse(pm.checkEquivalence(pc1, pc2));
	}
}
