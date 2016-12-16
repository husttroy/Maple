package edu.ucla.cs.process;

import static org.junit.Assert.*;

import java.util.HashSet;
import java.util.Set;

import org.junit.Test;

import com.google.common.collect.Multimap;

import edu.ucla.cs.slice.Slicer;

public class SlicerTest{
	final String mkey = "https://github.com/fywb251/bsl_impc_android ** cube-android/src/com/foreveross/chameleon/pad/fragment/ChatRoomFragment.java ** ChatRoomFragment ** initValues";
	
	@Test
	public void testPattern() {
		String s = "TRY {;IF {;IF {;};new File;exists;IF {;createNewFile;};};};CATCH {;};";
		String pattern = "IF \\{;\\};|ELSE \\{;\\};|LOOP \\{;\\};|TRY \\{;\\};(CATCH \\{;\\};)*(FINALLY \\{;\\};)*";
		String a = s.replaceAll(pattern, "");
		assertEquals("TRY {;IF {;new File;exists;IF {;createNewFile;};};};CATCH {;};", a);
	}
	
	@Test
	public void testSlicer() {
		Set<String> api_query = new HashSet<String>();
		api_query.add("createNewFile");
		
		Slicer.setup();
		Multimap<String, String> seqs = Slicer.slice(api_query);
		System.out.println(seqs.get(mkey).toString());
		assertEquals("[new File, exists, IF {, TRY {, createNewFile, }, CATCH {, }, }]", 
				seqs.get(mkey).toString());
	}
}