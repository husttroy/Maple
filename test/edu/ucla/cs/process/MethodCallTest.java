package edu.ucla.cs.process;

import static org.junit.Assert.*;

import org.junit.Test;

import com.google.common.collect.HashMultiset;
import com.google.common.collect.Multiset;

import edu.ucla.cs.model.MethodCall;

public class MethodCallTest {
	
	@Test
	public void testEquals(){
		MethodCall mock1 = new MethodCall("new File", "v::path");
		MethodCall mock2 = new MethodCall("new File", "v::path");
		assertEquals(true, mock1.equals(mock2));
	}
	
	@Test
	public void testWithMultiset(){
		MethodCall mock1 = new MethodCall("new File", "v::path");
		MethodCall mock2 = new MethodCall("new File", "v::path");
		Multiset<MethodCall> mset = HashMultiset.create();
		mset.add(mock1);
		assertEquals(true, mset.contains(mock1));
		assertEquals(true, mset.contains(mock2));
	}
}
