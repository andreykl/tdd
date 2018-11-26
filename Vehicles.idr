module Vehicles

data PowerSource = Pedal | Petrol | Electicity

data Vehicle : PowerSource -> Type where
  Unicyle : Vehicle Pedal
  Bicycle : Vehicle Pedal
  Motocycle : (fuel : Nat) -> Vehicle Petrol
  Car : (fuel : Nat) -> Vehicle Petrol
  Bus : (fuel : Nat) -> Vehicle Petrol
  Tram : Vehicle Electicity
  ElectricCar : Vehicle Electicity

total
wheels : Vehicle power -> Int
wheels Unicyle = 1
wheels Bicycle = 2
wheels Motocycle = 2
wheels (Car fuel) = 4
wheels (Bus fuel) = 4

total
refuel : Vehicle Petrol -> Vehicle Petrol
refuel (Motocycle fuel) = Motocycle 20
refuel (Car fuel) = Car 100
refuel (Bus fuel) = Bus 200
