package edu.ucla.cs.process.traditional;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.HashMap;
import java.util.Set;

import edu.ucla.cs.model.Method;
import edu.ucla.cs.slice.Slicer;

public class Process {
		public static HashMap<String, Method> methods = new HashMap<String, Method>();
		
		// use strategy design pattern
		public ProcessStrategy s;
		
		public void processByLine(String path) throws IOException {
			File f = new File(path);
			try (BufferedReader br = new BufferedReader(new FileReader(f))){
				String line = null;
			    while ((line = br.readLine()) != null) {
			        //process each line based on the strategy
			        s.process(line);
			    }      
			}
		}
		
		/**
		 * Cross-check the result of the traditional analysis with the light-weight analysis
		 */
		public void crosscheck() {
			Slicer.setup();
			
			Set<String> set1 = Slicer.methods.keySet();
			Set<String> set2 = methods.keySet();
			System.out.println("Seqeunces detected by the lightweight apporach but not the traditional approach");
			for(String s : set1) {
				s = s.replaceAll(" \\*\\* ", "!");
				if(!set2.contains(s)) {
					System.out.println(s);
				}
			}
			System.out.println("Seqeunces detected by the traditional apporach but not the lightweight approach");
			for(String s : set2) {
				s = s.replaceAll("\\!", " ** ");
				if(!set1.contains(s)) {
					System.out.println(s);
				}
			}
		}
		
		public static void main(String[] args) {
			Process p = new Process();
			try {
				p.s = new SequenceProcessor();
				p.processByLine("/home/troy/research/BOA/Maple/example/new_sequence.txt");
				
				// cross-check
				// p.crosscheck();
				
				// print the split method calls
				for(String key : methods.keySet()) {
					System.out.println(key.replaceAll("\\!", " ** ") + "---" + methods.get(key).seq);
				}
			} catch(IOException e) {
				e.printStackTrace();
			}
		}
}
