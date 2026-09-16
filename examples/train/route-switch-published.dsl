package railway {
  enum Position {
    FAILURE;
    STRAIGHT;
    DIVERGING;
  }

  abstract class RailwayElement {
    id : Integer [0..1] ordered unique;
  }

  abstract class TrackElement extends railway::RailwayElement {
  }

  class Route extends railway::RailwayElement {
    active : Boolean [0..1] ordered unique;
    follows : railway::SwitchPosition [0..*] ordered unique composite;
    requires : railway::Sensor [2..*] ordered unique;
  }

  class Sensor extends railway::RailwayElement {
  }

  class Switch extends railway::TrackElement {
    currentPosition : enum railway::Position [0..1] ordered unique;
    positions : railway::SwitchPosition [0..*] ordered unique;
  }

  class SwitchPosition extends railway::RailwayElement {
    position : enum railway::Position [0..1] ordered unique;
    route : railway::Route [1..1] ordered unique;
    target : railway::Switch [1..1] ordered unique;
  }

  association RouteFollows {
    ends railway::Route::follows, railway::SwitchPosition::route;
  }

  association SwitchPositions {
    ends railway::Switch::positions, railway::SwitchPosition::target;
  }
}

object route : railway::Route {
  observe railway::RailwayElement::id = [101];
  observe railway::Route::active = [true];
  observe railway::Route::follows = [@switchPosition];
  observe railway::Route::requires = [@sensorA, @sensorB];
}

object switch : railway::Switch {
  observe railway::RailwayElement::id = [202];
  observe railway::Switch::currentPosition = [railway::Position::STRAIGHT];
  observe railway::Switch::positions = [@switchPosition];
}

object switchPosition : railway::SwitchPosition {
  observe railway::RailwayElement::id = [303];
  observe railway::SwitchPosition::position = [railway::Position::STRAIGHT];
  observe railway::SwitchPosition::route = [@route];
  observe railway::SwitchPosition::target = [@switch];
}

object sensorA : railway::Sensor {
  observe railway::RailwayElement::id = [404];
}

object sensorB : railway::Sensor {
  observe railway::RailwayElement::id = [405];
}
