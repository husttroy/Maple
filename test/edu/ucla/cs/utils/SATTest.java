package edu.ucla.cs.utils;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.junit.Test;

public class SATTest {
	
	@Test
	public void testStripOffUnnecessaryParentheses() {
		SAT sat = new SAT();
		String rel = sat.stripUnnecessaryParentheses("(rcv.exists())");
		assertEquals("rcv.exists()", rel);
	}
	
	@Test
	public void testSymbolizeBasic() {
		SAT sat = new SAT();
		String rel = sat.symbolize("!rcv.exists()");
		assertEquals("!b0", rel);
	}
	
	@Test
	public void testSymbolizeBasicWithArg() {
		SAT sat = new SAT();
		String rel = sat.symbolize("!rcv.exists(c)");
		assertEquals("!b0", rel);
	}
	
	@Test
	public void testSymbolizeDoubleNegation() {
		SAT sat = new SAT();
		String rel = sat.symbolize("!(!rcv.exists()) && !rcv.exists()");
		assertEquals("!(!b0) && !b0", rel);
	}

	@Test
	public void testSymbolizeWithUncessaryParentheses() {
		SAT sat = new SAT();
		String rel = sat.symbolize("!(rcv.exists())");
		assertEquals("!b0", rel);
	}

	@Test
	public void testSymbolizeWithUnbalancedParentheses() {
		SAT sat = new SAT();
		String rel = sat
				.symbolize("((s.length() + 1 > 0) || flag) && Environment.SSS");
		assertEquals("((i0 + 1 > 0) || b0) && b1", rel);
	}

	@Test
	public void testSymbolizeBug1() {
		SAT sat = new SAT();
		String p1 = "rcv.size()<firstSet.size()";
		String p2 = "true&&rcv!=null&&rcv.size()>0";
		String p1_sym = sat.symbolize(p1);
		String p2_sym = sat.symbolize(p2);
		assertEquals("i0<i1", p1_sym);
		assertEquals("true&&i2!=0&&i0>0", p2_sym);
	}
	
	/**
	 * http://stackoverflow.com/questions/12625038
	 */
	@Test
	public void testSymbolizePredicateWithParameterizedTypes() {
		SAT sat = new SAT();
		String p1 = "new ArrayList<>(rcv).size()>0";
		String p1_sym = sat.symbolize(p1);
		assertEquals("i0>0", p1_sym);
	}
	
	@Test
	public void testSymbolizeWithLiterals() {
		SAT sat = new SAT();
		String rel = sat.symbolize("((s.length() + 1 > 0) || (true)) && false");
		assertEquals("((i0 + 1 > 0) || true) && false", rel);
	}
	
	@Test
	public void testZ3QueryGeneration() {
		SAT sat = new SAT();
		String p1 = "(! (== 1 a0))";
		String p2 = "(&& b0 b2)";
		String query = "(assert (or (and (not (= 1 a0)) (not (and b0 b2))) (and (not (not (= 1 a0))) (and b0 b2))))\n(check-sat)";
		assertEquals(query, sat.generateEquvalenceQueryInZ3(p1, p2));
	}
	
	@Test
	public void testZ3Runner() {
		SAT sat = new SAT();
		String query = "(declare-const a0 Int)\n(declare-const b0 Bool)\n(declare-const b2 Bool)(assert (and (not (= 1 a0)) (not (and b0 b2))))\n(check-sat)";
		assertTrue(sat.isSAT(query));
	}
	
	@Test
	public void testEquivalenceChecker() {
		SAT sat = new SAT();
		assertTrue(sat.checkEquivalence("true && arg0 >= 1 && !(rcv.exists())",
				"1 <= arg0 && !rcv.exists()"));
	}

	@Test
	public void testEquivalenceWithFalse() {
		SAT sat = new SAT();
		assertFalse(sat.checkEquivalence("false", "1 <= arg0 && !rcv.exists()"));
	}

	@Test
	public void testEquivalenceWithTrue() {
		SAT sat = new SAT();
		assertFalse(sat.checkEquivalence("true && arg0 >= 1 && !(rcv.exists())",
				"true"));
	}
	
	@Test
	public void testImplicationChecker() {
		SAT sat = new SAT();
		assertTrue(sat.checkImplication("a&&c", "a"));
		assertFalse(sat.checkImplication("a", "a&&c"));
	}
}
