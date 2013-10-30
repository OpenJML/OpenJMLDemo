
public class IgnitionModule {
	
	SensorValue rpmSensor;
	LookupScale rpmScale = new LookupScale(600, 8000, 16);
	LookupTable1d ignitionTable = new LookupTable1d(rpmScale,
		new int[] { 120, 80, 60, 80, 100, 120, 140, 160, 180, 200, 220, 250, 300, 320, 340, 360	
	});
	
	public IgnitionModule(SensorValue rpmSensor) {
		this.rpmSensor = rpmSensor;
	}
	
	int getIgnition() {
		return ignitionTable.getValue(rpmSensor);

	}

}
