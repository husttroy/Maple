package edu.ucla.cs.process;

import static org.junit.Assert.assertEquals;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Iterator;

import org.junit.Before;
import org.junit.Test;

import com.google.common.collect.Multiset;

import edu.ucla.cs.model.Assignment;
import edu.ucla.cs.model.MethodCall;
import edu.ucla.cs.model.Predicate;
import edu.ucla.cs.model.Receiver;
import edu.ucla.cs.slice.Slicer;

public class ProcessDriver {
	final String key = "https://github.com/fywb251/bsl_impc_android ** cube-android/src/com/foreveross/chameleon/pad/fragment/ChatRoomFragment.java ** ChatRoomFragment ** initValues";
	
	Process proc;
	
	@Before
	public void setup(){
		proc = new Process();
	}
	
	@Test
	public void test1(){
		try {
			proc.s = new TypeProcessor(); 
			proc.processByLine("/home/troy/research/BOA/Slicer/example/type.txt");
			String type = Slicer.methods.get(key).locals.get("dir");
			assertEquals("File", type);
		} catch (IOException e) {
			e.printStackTrace();
		}
		
	}
	
	@Test
	public void test2(){
		try {
			proc.s = new SequenceProcessor();
			proc.processByLine("/home/troy/research/BOA/Slicer/example/sequence.txt");
			String m1 = Slicer.methods.get(key).seq.get(0);
			assertEquals("IF {", m1);
			boolean b1 = Slicer.methods.get(key).seq.contains("createNewFile");
			
			assertEquals(true, b1);
			boolean b2 = Slicer.methods.get(key).seq.contains("mkdirs");
			
			assertEquals(true, b2);
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
	
	@Test
	public void test3() {
		try {
			proc.s = new ArgumentProcessor();
			proc.processByLine("/home/troy/research/BOA/Slicer/example/argument.txt");
			Multiset<MethodCall> mset = Slicer.methods.get(key).calls.get("new File");
			
			assertEquals(3, mset.size());
			assertEquals(2, mset.elementSet().size());
			
			// mock objects
			MethodCall mock = new MethodCall("new File", "v::path");
			assertEquals(2, mset.count(mock));
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
	
	@Test
	public void test4() {
		try {
			proc.s = new AssignmentProcessor();
			proc.processByLine("/home/troy/research/BOA/Slicer/example/assignment.txt");
			Multiset<Assignment> mset = Slicer.methods.get(key).assigns.get("dir");
			
			assertEquals(1, mset.size());
			
			// mock objects
			Assignment mock = new Assignment("dir", "|new File|path");
			assertEquals(1, mset.count(mock));
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
	
	@Test
	public void test5() {
		try {
			proc.s = new ReceiverProcessor();
			proc.processByLine("/home/troy/research/BOA/Slicer/example/receiver.txt");
			Multiset<Receiver> mset = Slicer.methods.get(key).receivers.get("exists");
			
			assertEquals(3, mset.size());
			
			// mock objects
			Receiver mock = new Receiver("dir", "exists");
			assertEquals(1, mset.count(mock));
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
	
	@Test
	public void test6() {
		try {
			proc.s = new PredicateProcessor();
			proc.processByLine("/home/troy/research/BOA/Slicer/example/predicate.txt");
			Multiset<Predicate> mset = Slicer.methods.get(key).predicates.get("createNewFile");
			
			assertEquals(1, mset.size());
			
			// mock objects
			Predicate mock = new Predicate("createNewFile", "!exists");
			assertEquals(1, mset.count(mock));
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
}
