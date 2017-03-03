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
}
