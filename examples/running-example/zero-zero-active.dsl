package railway {
  enum Position {
    FAILURE;
    STRAIGHT;
    DIVERGING;
  }
  enum Signal {
    FAILURE;
    STOP;
    GO;
  }
  abstract class RailwayElement {
    id : Integer [0..1] ordered nonunique;
  }
  class RailwayContainer {
    routes : railway::Route [0..*] ordered unique composite;
    regions : railway::Region [0..*] ordered unique composite;
  }
  class Region extends railway::RailwayElement {
    sensors : railway::Sensor [0..*] ordered unique composite;
    elements : railway::TrackElement [0..*] ordered unique composite;
  }
  class Route extends railway::RailwayElement {
    active : Boolean [0..0] ordered nonunique;
    follows : railway::SwitchPosition [0..*] ordered unique composite;
    requires : railway::Sensor [2..*] ordered unique;
    entry : railway::Semaphore [0..1] ordered unique;
    exit : railway::Semaphore [0..1] ordered unique;
  }
  class Sensor extends railway::RailwayElement {
    monitors : railway::TrackElement [0..*] ordered unique;
  }
  abstract class TrackElement extends railway::RailwayElement {
    monitoredBy : railway::Sensor [0..*] ordered unique;
    connectsTo : railway::TrackElement [0..*] ordered unique;
  }
  class Segment extends railway::TrackElement {
    length : Integer [0..1] ordered nonunique;
    semaphores : railway::Semaphore [0..*] ordered unique composite;
  }
  class Switch extends railway::TrackElement {
    currentPosition : enum railway::Position [0..1] ordered nonunique;
    positions : railway::SwitchPosition [0..*] ordered unique;
  }
  class SwitchPosition extends railway::RailwayElement {
    position : enum railway::Position [0..1] ordered nonunique;
    route : railway::Route [0..1] ordered unique;
    target : railway::Switch [0..1] ordered unique;
  }
  class Semaphore extends railway::RailwayElement {
    signal : enum railway::Signal [0..1] ordered nonunique;
  }
  association follows__route {
    ends railway::Route::follows, railway::SwitchPosition::route;
  }
  association monitors__monitoredBy {
    ends railway::Sensor::monitors, railway::TrackElement::monitoredBy;
  }
  association positions__target {
    ends railway::Switch::positions, railway::SwitchPosition::target;
  }
}

object r : railway::Route {
  observe railway::RailwayElement::id = [101];
  observe railway::Route::active = [];
  observe railway::Route::follows = [@sp];
  observe railway::Route::requires = [@sA, @sB];
  observe railway::Route::entry = [];
  observe railway::Route::exit = [];
}
object sw : railway::Switch {
  observe railway::RailwayElement::id = [202];
  observe railway::TrackElement::monitoredBy = [];
  observe railway::TrackElement::connectsTo = [];
  observe railway::Switch::currentPosition = [railway::Position::STRAIGHT];
  observe railway::Switch::positions = [@sp];
}
object sp : railway::SwitchPosition {
  observe railway::RailwayElement::id = [303];
  observe railway::SwitchPosition::position = [railway::Position::STRAIGHT];
  observe railway::SwitchPosition::route = [@r];
  observe railway::SwitchPosition::target = [@sw];
}
object sA : railway::Sensor {
  observe railway::RailwayElement::id = [404];
  observe railway::Sensor::monitors = [];
}
object sB : railway::Sensor {
  observe railway::RailwayElement::id = [405];
  observe railway::Sensor::monitors = [];
}
