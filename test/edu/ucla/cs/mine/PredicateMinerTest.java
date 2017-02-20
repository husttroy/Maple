package edu.ucla.cs.mine;

import static org.junit.Assert.*;

import java.util.ArrayList;
import java.util.HashSet;

import org.junit.Test;

import edu.ucla.cs.model.PredicateCluster;

public class PredicateMinerTest {
	@Test
	public void testConditionOne() {
		PredicateMiner pm = new PredicateMiner(new ArrayList<String>());
		HashSet<String> vars = new HashSet<String>();
		vars.add("a");
		assertEquals(pm.condition(vars, "a && b"), "a && true");
	}

	@Test
	public void testConditionAll() {
		PredicateMiner pm = new PredicateMiner(new ArrayList<String>());
		HashSet<String> vars = new HashSet<String>();
		vars.add("a");
		vars.add("b");
		assertEquals(pm.condition(vars, "a && b"), "a && b");
	}

	@Test
	public void testConditionNone() {
		PredicateMiner pm = new PredicateMiner(new ArrayList<String>());
		HashSet<String> vars = new HashSet<String>();
		vars.add("c");
		assertEquals(pm.condition(vars, "a && b"), "true && true");
	}

	@Test
	public void testConditionNestedPredicate1() {
		PredicateMiner pm = new PredicateMiner(new ArrayList<String>());
		HashSet<String> vars = new HashSet<String>();
		vars.add("c");
		assertEquals(pm.condition(vars, "(a || b) && c"), "(true || true) && c");
	}

	@Test
	public void testConditionNestedPredicate2() {
		PredicateMiner pm = new PredicateMiner(new ArrayList<String>());
		HashSet<String> vars = new HashSet<String>();
		vars.add("c");
		assertEquals(pm.condition(vars, "((a + b > 0) || c) && d"),
				"(true || c) && true");
		vars.add("a");
		assertEquals(pm.condition(vars, "((a + b > 0) || c) && d"),
				"((a + b > 0) || c) && true");
	}

	@Test
	public void testSymbolizeBasic() {
		PredicateMiner pm = new PredicateMiner(new ArrayList<String>());
		String rel = pm.symbolize("!rcv.exists");
		assertEquals("!b0", rel);
	}

	@Test
	public void testSymbolizeWithUncessaryParentheses() {
		PredicateMiner pm = new PredicateMiner(new ArrayList<String>());
		String rel = pm.symbolize("!(rcv.exists)");
		assertEquals("!b0", rel);
	}

	@Test
	public void testSymbolizeWithUnbalancedParentheses() {
		PredicateMiner pm = new PredicateMiner(new ArrayList<String>());
		String rel = pm
				.symbolize("((s.length + 1 > 0) || flag) && Environment.SSS");
		assertEquals("((i0 + 1 > 0) || b0) && b1", rel);
	}

	@Test
	public void testSymbolizeWithLiterals() {
		PredicateMiner pm = new PredicateMiner(new ArrayList<String>());
		String rel = pm.symbolize("((s.length + 1 > 0) || (true)) && false");
		assertEquals("((i0 + 1 > 0) || true) && false", rel);
	}

	@Test
	public void testZ3QueryGeneration() {
		PredicateMiner pm = new PredicateMiner(new ArrayList<String>());
		String p1 = "(! (== 1 a0))";
		String p2 = "(&& b0 b2)";
		String query = "(assert (or (and (not (= 1 a0)) (not (and b0 b2))) (and (not (not (= 1 a0))) (and b0 b2))))\n(check-sat)";
		assertEquals(query, pm.generateZ3Query(p1, p2));
	}

	@Test
	public void testZ3Runner() {
		PredicateMiner pm = new PredicateMiner(new ArrayList<String>());
		String query = "(declare-const a0 Int)\n(declare-const b0 Bool)\n(declare-const b2 Bool)(assert (and (not (= 1 a0)) (not (and b0 b2))))\n(check-sat)";
		assertTrue(pm.isSAT(query));
	}
	
	@Test
	public void testEquivalenceChecker() {
		PredicateMiner pm = new PredicateMiner(new ArrayList<String>());
		PredicateCluster pc1 = new PredicateCluster("true && arg0 >= 1 && !(rcv.exists)", 1);
		PredicateCluster pc2 = new PredicateCluster("1 <= arg0 && !rcv.exists", 1);
		assertTrue(pm.checkEquivalence(pc1, pc2));
	}
	
	@Test
	public void testEquivalenceWithFalse() {
		PredicateMiner pm = new PredicateMiner(new ArrayList<String>());
		PredicateCluster pc1 = new PredicateCluster("false", 1);
		PredicateCluster pc2 = new PredicateCluster("1 <= arg0 && !rcv.exists", 1);
		assertFalse(pm.checkEquivalence(pc1, pc2));
	}
	
	@Test
	public void testEquivalenceWithTrue() {
		PredicateMiner pm = new PredicateMiner(new ArrayList<String>());
		PredicateCluster pc1 = new PredicateCluster("true && arg0 >= 1 && !(rcv.exists)", 1);
		PredicateCluster pc2 = new PredicateCluster("true", 1);
		assertFalse(pm.checkEquivalence(pc1, pc2));
	}
}
