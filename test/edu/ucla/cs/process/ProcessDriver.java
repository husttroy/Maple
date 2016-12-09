package edu.ucla.cs.process;

import java.io.IOException;

import edu.ucla.cs.slice.Slicer;

public class ProcessDriver {
	public static void main(String[] args){
		Process proc = new Process();
		try {
			proc.processByLine("/home/troy/research/BOA/Slicer/example/type.txt");
			String type = Slicer.methods.get("https://github.com/fywb251/bsl_impc_android * cube-android/src/com/foreveross/chameleon/pad/fragment/ChatRoomFragment.java * ChatRoomFragment * initValues").locals.get("dir");
			System.out.println(type);
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
}
