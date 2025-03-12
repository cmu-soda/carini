package recomp;

import java.io.BufferedReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;

import tlc2.Utils;

public class NegTraceGen {
	private final long MAX_ADDITIONAL_TIMEOUT = 1000L * 60L * 5L; // 5 min
	private final Lock lock = new ReentrantLock();

	public List<String> generate(final String tla, final String cfg, final String detectError,
			boolean extendedNegTraceSearch, long timeout, final String tlcJarPath) {
		try {
			// TODO should use a temporary file for <cexTraceOutputFile>
			List<String> tlcOutputLines = new ArrayList<>();
			PerfTimer timer = new PerfTimer();
			final String[] regularCmd = {"java", "-jar", tlcJarPath, "-cleanup", "-deadlock", "-workers", "auto", "-config", cfg, tla};
			final String[] extendedCmd = {"java", "-jar", tlcJarPath, "-cleanup", "-deadlock", "-continue", "-workers", "auto", "-config", cfg, tla};
			final String[] cmd = extendedNegTraceSearch ? extendedCmd : regularCmd;
			Process proc = Runtime.getRuntime().exec(cmd);
			
			// start a new thread for capturing the otput of TLC. the thread will wait until an error occurs;
			// if it does, it will wait an additional period of time to find as many more errors errors as possible.
			new Thread() {
			    public void run() {
			    	BufferedReader inputReader = proc.inputReader();
			    	String line = null;
			    	boolean noViolations = true;
			        try {
						while ((line = inputReader.readLine()) != null) {
							try {
								lock.lock();
								tlcOutputLines.add(line);
							}
							finally {
								lock.unlock();
							}
							// when we encounter the first instance of an error, start a countdown of until we
							// forcibly shutdown the process (only in extendedNegTraceSearch mode).
							if (extendedNegTraceSearch && noViolations && line.contains(detectError)) {
								noViolations = false;
								new Thread() {
								    public void run() {
								        try {
								        	final long timeout = Math.min(MAX_ADDITIONAL_TIMEOUT, timer.timeElapsed()); // an extra 100%
											sleep(timeout);
											if (proc.isAlive()) {
												proc.destroyForcibly();
											}
										} catch (InterruptedException e) {}
								    }
								}.start();
							}
						}
					} catch (IOException e) {}
			    }
			}.start();
			
			proc.waitFor(timeout, TimeUnit.MINUTES);
			
			// kill TLC if it's still running
			if (proc.isAlive()) {
				proc.destroyForcibly();
			}
			
			// clean up the states dir
			lock.lock();
			rmrf("states/");
			return new ArrayList<>(tlcOutputLines);
		}
		catch (Exception e) {
			e.printStackTrace();
			Utils.assertTrue(false, "Exception while generating a cex!");
		}
		finally {
			lock.unlock();
		}
		return null;
	}
	
	private static void rmrf(final String path) {
		try {
			final String[] rmStatesCmd = {"sh", "-c", "rm -rf " + path};
			Runtime.getRuntime().exec(rmStatesCmd);
		} catch (IOException e) {}
	}
}
