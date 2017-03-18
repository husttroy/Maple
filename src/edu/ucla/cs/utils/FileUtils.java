package edu.ucla.cs.utils;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.BufferedReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashSet;

public class FileUtils {
	
	public static String readFileToString(String path){
		String content = "";
		try (BufferedReader br = new BufferedReader(new FileReader(new File(path)))){
			String line = null;
			while((line = br.readLine()) != null) {
				content += line + System.lineSeparator();
			}
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} catch (IOException e) {
			e.printStackTrace();
		}
		
		return content;
	}
	
	public static void writeStringToFile(String s, String path) {
		try {
			File f = new File(path);
			FileWriter w = new FileWriter(f, false);
			BufferedWriter writer = new BufferedWriter(w);
			writer.write(s);
			writer.flush();
			writer.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
	
	public static void writeArrayToFile(ArrayList<String> ss, String path) {
		String content = "";
		for(int i = 0; i < ss.size() - 1; i++) {
			content += ss.get(i) + System.lineSeparator();
		}
		
		if(ss.size() - 1 >= 0) {
			content += ss.get(ss.size() - 1);
		}
		
		writeStringToFile(content, path);;
	}
	
	public static int countLines(String path) {
		int count = 0;
		try (BufferedReader br = new BufferedReader(new FileReader(new File(path)))){
			while(br.readLine()!=null) {
				count++;
			}
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} catch (IOException e) {
			e.printStackTrace();
		}
		
		return count;
	}
	
	public static void delete(String path) {
		File f = new File(path);
		if(f.exists()) {
			f.delete();
		}
	}
	
	public static void removeLines(String path, HashSet<String> lines) {
		File file = new File(path);
		File temp = new File(path + ".temp");
		
		if(temp.exists()) {
			temp.delete();
		}
		
		try {
			temp.createNewFile();
		} catch (IOException e1) {
			e1.printStackTrace();
		}
		
		BufferedReader reader = null;
		BufferedWriter writer = null;
		try {
			reader = new BufferedReader(new FileReader(file));
			writer = new BufferedWriter(new FileWriter(temp));
			String line;
			while((line = reader.readLine()) != null) {
				if(lines.contains(line)) {
					continue;
				}
				
				writer.write(line + System.lineSeparator());
			}
		} catch (IOException e) {
			e.printStackTrace();
		} finally {
			if(reader != null) {
				try {
					reader.close();
				} catch (IOException e) {
					e.printStackTrace();
				}
			}
			if(writer != null) {
				try {
					writer.close();
				} catch (IOException e) {
					e.printStackTrace();
				}
			}
		}
		
		temp.renameTo(file);
	}

}
